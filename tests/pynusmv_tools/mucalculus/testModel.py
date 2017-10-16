import unittest

from pynusmv.dd import BDD
from pynusmv.init import init_nusmv, deinit_nusmv
from pynusmv.mc import eval_simple_expression
from pynusmv import node

from pynusmv_tools.mucalculus import model, UnknownTransitionError


class TestModel(unittest.TestCase):
    
    def setUp(self):
        init_nusmv()
    
    def tearDown(self):
        model.reset_globals()
        deinit_nusmv()
    
    def test_no_time(self):
        smvmodel = """
        MODULE main
            VAR state: {s1, s2};
            INIT state = s1
            TRANS next(state) = s2
        """
        model.load_from_string(smvmodel)
        fsm = model.bddModel()
        self.assertSetEqual(set(fsm.transitions.keys()), {'time'})
        self.assertEqual(fsm.post(fsm.init, 'time'),
                         eval_simple_expression(fsm, 'state = s2'))
    
    def test_one_transition(self):
        smvmodel = """
        MODULE main
            VAR state: {s1, s2};
            INIT state = s1
            TRANS next(state) = s2
        """
        model.load_from_string(smvmodel)
        fsm = model.bddModel()
        self.assertSetEqual(set(fsm.transitions.keys()), {'time'})
        self.assertEqual(fsm.post(fsm.init, transition='time'),
                         eval_simple_expression(fsm, 'state = s2'))
    
    def test_inputs(self):
        smvmodel = """
        MODULE main
            VAR state: {s1, s2};
            IVAR run: boolean;
            INIT state = s1
            TRANS next(state) = (run ? s2 : state)
        """
        model.load_from_string(smvmodel)
        fsm = model.bddModel()
        self.assertSetEqual(set(fsm.transitions.keys()), {'time'})
        self.assertEqual(fsm.post(fsm.init, transition='time'),
                         eval_simple_expression(fsm,
                                                'state = s2 | state = s1'))
        
        run = eval_simple_expression(fsm, "run")
        self.assertEqual(fsm.post(fsm.init, inputs=run),
                         eval_simple_expression(fsm,
                                                'state = s2'))
        
        nrun = eval_simple_expression(fsm, "!run")
        self.assertEqual(fsm.post(fsm.init, inputs=nrun),
                         eval_simple_expression(fsm,
                                                'state = s1'))
    
    def test_several_transitions(self):
        smvmodel = """
        MODULE main
            VAR state: {s1, s2};
            IVAR transition : {time, knowledge};
            INIT state = s1
            TRANS case transition = time : next(state) = s2;
                       transition = knowledge : next(state) = state;
                  esac
        """
        model.load_from_string(smvmodel)
        fsm = model.bddModel()
        self.assertSetEqual(set(fsm.transitions.keys()), {'time', 'knowledge'})
        self.assertEqual(fsm.post(fsm.init, transition='time'),
                         eval_simple_expression(fsm, 'state = s2'))
        self.assertEqual(fsm.post(fsm.init, transition='knowledge'),
                         eval_simple_expression(fsm, 'state = s1'))
        
        with self.assertRaises(UnknownTransitionError):
            fsm.post(fsm.init, 'unknown')
    
    
    def test_additional_transitions(self):
        smvmodel = """
        MODULE main
            VAR state: {s1, s2};
            IVAR transition : {time, knowledge};
            INIT state = s1
            TRANS case transition = time : next(state) = s2;
                       transition = knowledge : next(state) = state;
                  esac
        """
        model.load_from_string(smvmodel)
        transitions = {'reset': 'next(state) = s1'}
        fsm = model.bddModel(transitions=transitions)
        self.assertSetEqual(set(fsm.transitions.keys()),
                            {'time', 'knowledge', 'reset'})
        self.assertEqual(fsm.post(fsm.init, 'time'),
                         eval_simple_expression(fsm, 'state = s2'))
        self.assertEqual(fsm.post(fsm.init, 'knowledge'),
                         eval_simple_expression(fsm, 'state = s1'))
        self.assertEqual(fsm.post(fsm.reachable_states, 'reset'),
                         eval_simple_expression(fsm, 'state = s1'))