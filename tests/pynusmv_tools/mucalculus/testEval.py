import unittest

from pynusmv.dd import BDD
from pynusmv.init import init_nusmv, deinit_nusmv
from pynusmv.mc import eval_simple_expression

from pynusmv_tools.mucalculus import model
from pynusmv_tools.mucalculus.formula import (MTrue, MFalse, Variable,
                                          Atom, Not, And, Or,
                                          Diamond, Box, Mu, Nu)


class TestEval(unittest.TestCase):
    
    def setUp(self):
        init_nusmv()
    
    def tearDown(self):
        model.reset_globals()
        deinit_nusmv()
        
    def cardgame(self):
        model.load_from_file("tests/pynusmv_tools/mucalculus/models/cardgame.smv")
        fsm = model.bddModel()
        self.assertIsNotNone(fsm)
        return fsm
        
    def show_si(self, fsm, bdd):
        if bdd.isnot_false():
            sis = fsm.pick_all_states_inputs(bdd)
            print("SI count:", len(sis))
            for si in sis:
                print(si.get_str_values())
            
    def show_s(self, fsm, bdd):
        if bdd.isnot_false():
            ss = fsm.pick_all_states(bdd)
            print("S count:", len(ss))
            for s in ss:
                print(s.get_str_values())
            
    def show_i(self, fsm, bdd):
        if bdd.isnot_false():
            iss = fsm.pick_all_inputs(bdd)
            print("I count:", len(iss))
            for i in iss:
                print(i.get_str_values())


    def test_eval_simple(self):
        fsm = self.cardgame()
        
        pa = eval_simple_expression(fsm, "pcard = Ac")
        true = eval_simple_expression(fsm, "TRUE")
        false = eval_simple_expression(fsm, "FALSE")
        
        self.assertEqual(true, MTrue().eval(fsm))
        self.assertEqual(false, MFalse().eval(fsm))
        self.assertEqual(pa, Atom("pcard = Ac").eval(fsm))
    
    
    def test_eval_boolean(self):
        fsm = self.cardgame()
        
        s0 = eval_simple_expression(fsm, "step = 0")
        s1 = eval_simple_expression(fsm, "step = 1")
        pa = eval_simple_expression(fsm, "pcard = Ac")
        win = eval_simple_expression(fsm, "win")
        
        self.assertEqual(s0 & s1, And(Atom("step = 0"), Atom("step = 1")).eval(fsm))
        self.assertEqual(s0 | s1, Or(Atom("step = 0"), Atom("step = 1")).eval(fsm))
        self.assertEqual(~win, Not(Atom("win")).eval(fsm))
    
    
    def test_eval_diamond(self):
        fsm = self.cardgame()
        
        s0 = eval_simple_expression(fsm, "step = 0")
        s1 = eval_simple_expression(fsm, "step = 1")
        s2 = eval_simple_expression(fsm, "step = 2")
        pa = eval_simple_expression(fsm, "pcard = Ac")
        pk = eval_simple_expression(fsm, "pcard = K")
        pq = eval_simple_expression(fsm, "pcard = Q")
        da = eval_simple_expression(fsm, "dcard = Ac")
        dk = eval_simple_expression(fsm, "dcard = K")
        dq = eval_simple_expression(fsm, "dcard = Q")
        dda = eval_simple_expression(fsm, "ddcard = Ac")
        ddk = eval_simple_expression(fsm, "ddcard = K")
        ddq = eval_simple_expression(fsm, "ddcard = Q")
        win = eval_simple_expression(fsm, "win")
        lose = eval_simple_expression(fsm, "lose")
        true = eval_simple_expression(fsm, "TRUE")
        false = eval_simple_expression(fsm, "FALSE")
        
        self.assertEqual(s0, Diamond(Atom("step = 1")).eval(fsm))
    
    
    def test_eval_box(self):
        fsm = self.cardgame()
        
        s0 = eval_simple_expression(fsm, "step = 0")
        s1 = eval_simple_expression(fsm, "step = 1")
        s2 = eval_simple_expression(fsm, "step = 2")
        pa = eval_simple_expression(fsm, "pcard = Ac")
        pk = eval_simple_expression(fsm, "pcard = K")
        pq = eval_simple_expression(fsm, "pcard = Q")
        da = eval_simple_expression(fsm, "dcard = Ac")
        dk = eval_simple_expression(fsm, "dcard = K")
        dq = eval_simple_expression(fsm, "dcard = Q")
        dda = eval_simple_expression(fsm, "ddcard = Ac")
        ddk = eval_simple_expression(fsm, "ddcard = K")
        ddq = eval_simple_expression(fsm, "ddcard = Q")
        win = eval_simple_expression(fsm, "win")
        lose = eval_simple_expression(fsm, "lose")
        true = eval_simple_expression(fsm, "TRUE")
        false = eval_simple_expression(fsm, "FALSE")
        
        self.assertTrue(s1 <=
                        Box(Atom("step = 2")).eval(fsm))
    
    
    def test_eval_fp(self):
        fsm = self.cardgame()
        
        s0 = eval_simple_expression(fsm, "step = 0")
        s1 = eval_simple_expression(fsm, "step = 1")
        s2 = eval_simple_expression(fsm, "step = 2")
        pa = eval_simple_expression(fsm, "pcard = Ac")
        pk = eval_simple_expression(fsm, "pcard = K")
        pq = eval_simple_expression(fsm, "pcard = Q")
        da = eval_simple_expression(fsm, "dcard = Ac")
        dk = eval_simple_expression(fsm, "dcard = K")
        dq = eval_simple_expression(fsm, "dcard = Q")
        dda = eval_simple_expression(fsm, "ddcard = Ac")
        ddk = eval_simple_expression(fsm, "ddcard = K")
        ddq = eval_simple_expression(fsm, "ddcard = Q")
        win = eval_simple_expression(fsm, "win")
        lose = eval_simple_expression(fsm, "lose")
        true = eval_simple_expression(fsm, "TRUE")
        false = eval_simple_expression(fsm, "FALSE")
        
        # mu Z. win | pre(Z)
        R = Mu(Variable("Z"), Or(Atom("win"), Diamond(Variable("Z"))))
        self.assertTrue(s0 <= R.eval(fsm))
        
        # nu Z. ~win & pre(Z)
        NW = Nu(Variable("Z"),
                And(Not(Atom("win")), Diamond(Variable("Z"))))
        self.assertTrue(NW.eval(fsm) <= ~win)