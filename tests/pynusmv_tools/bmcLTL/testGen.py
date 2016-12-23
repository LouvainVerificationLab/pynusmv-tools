'''
This test module validates the behavior of the SAT problem generation 
translating the bounded semantics verification of LTL properties as defined 
in :mod:`pynusmv_tools.bmcLTL.gen`
'''
from unittest                    import TestCase
from tests                       import utils as tests
from pynusmv_tools.bmcLTL                import gen

from pynusmv.bmc                 import ltlspec
from pynusmv.bmc                 import utils as bmcutils
from pynusmv.parser              import parse_ltl_spec
from pynusmv.node                import Node
from pynusmv.be.expression       import Be 
from pynusmv_tools.bmcLTL.parsing        import parseLTL
from pynusmv.sat                 import SatSolverFactory, Polarity,\
    SatSolverResult

class TestGen(TestCase):
 
    def test_model_problem(self):
        with tests.Configure(self, __file__, "/example.smv"):
            enc = self.enc
            # no step taken
            bound = 0
             
            tool  = gen.model_problem(self.befsm, bound)
            manual= enc.shift_to_time(self.befsm.init, 0)
             
            nusmv = bmcutils.BmcModel().path(bound, with_init=True)
             
            s_tool   = tests.canonical_cnf(tool)
            s_manual = tests.canonical_cnf(manual)
            s_nusmv  = tests.canonical_cnf(nusmv)
             
            self.assertEqual(s_tool, s_nusmv)
            self.assertEqual(s_tool, s_manual)
             
            # one step taken
            bound = 1
             
            tool  = gen.model_problem(self.befsm, bound)
            manual= enc.shift_to_time(self.befsm.trans,0) &\
                    enc.shift_to_time(self.befsm.init, 0)
             
            nusmv = bmcutils.BmcModel().path(bound, with_init=True)
             
            s_tool   = tests.canonical_cnf(tool)
            s_manual = tests.canonical_cnf(manual)
            s_nusmv  = tests.canonical_cnf(nusmv)
             
            self.assertEqual(s_tool, s_manual)
            self.assertEqual(s_tool, s_nusmv)
             
            # two steps
            bound = 2
             
            tool  = gen.model_problem(self.befsm, bound)
            manual= enc.shift_to_time(self.befsm.init, 0) &\
                    enc.shift_to_time(self.befsm.trans,0) &\
                    enc.shift_to_time(self.befsm.trans,1)
             
            nusmv = bmcutils.BmcModel().path(bound, with_init=True)
             
            s_tool   = tests.canonical_cnf(tool)
            s_manual = tests.canonical_cnf(manual)
            s_nusmv  = tests.canonical_cnf(nusmv)
             
            self.assertEqual(s_tool, s_manual)
            self.assertEqual(s_tool, s_nusmv)
    
    def verify_invariants_constraint(self, bound):
        model  = bmcutils.BmcModel() 
            
        manual = Be.true(self.mgr) 
        for i in range(bound+1):
            manual &= model.invar[i]
        
        tool = gen.invariants_constraint(self.befsm, bound)
        
        self.assertEqual(tests.canonical_cnf(tool), 
                         tests.canonical_cnf(manual))
        
    def test_invariants_constraint(self):
        with tests.Configure(self, __file__, "/example.smv"):
            self.verify_invariants_constraint(0)
            self.verify_invariants_constraint(1)
            self.verify_invariants_constraint(2)
            self.verify_invariants_constraint(3)
        
        with tests.Configure(self, __file__, "/dummy_with_invar.smv"):
            self.verify_invariants_constraint(0)
            self.verify_invariants_constraint(1)
            self.verify_invariants_constraint(2)
            self.verify_invariants_constraint(3)
    
    def satisfiability(self, problem):
        solver = SatSolverFactory.create()
        solver+= problem.to_cnf()
        solver.polarity(problem.to_cnf(), Polarity.POSITIVE)
        return solver.solve()
       
    def validate_generate_problem(self, bound, custom_text, nusmv_text):
        fsm     = self.befsm
        # formulae
        formula = parseLTL(custom_text)
        fml_node= Node.from_ptr(parse_ltl_spec(nusmv_text))
         
        # IMPORTANT NOTE: each instantiation of the problem creates new CNF 
        #   literal which appears in the clauses list (even in canonical form)
        #   hence, the canonical forms of the different instantiations cannot
        #   simply be compared as there is no a priori way to know what CNF 
        #   literal reconcile with what other.
        #   However, the different expressions should all have the exact same
        #   satisfiability. So, that's how this test proceeds.
          
        smv     = ltlspec.generate_ltl_problem(fsm, fml_node, bound)
        tool    = gen.generate_problem(formula, fsm, bound)
        manual  = gen.model_problem(fsm, bound) &\
                  formula.nnf(True).bounded_semantics(fsm, bound)
         
        sat_smv = self.satisfiability(smv)
        sat_tool= self.satisfiability(tool)
        sat_man = self.satisfiability(manual)
         
        self.assertEqual(sat_tool, sat_man)
        self.assertEqual(sat_tool, sat_smv)
         
    def test_generate_problem_nofairness_noinvars(self):
        with tests.Configure(self, __file__, "/example.smv"):
            # length 0
            self.validate_generate_problem(0, "<>(a <=> !b)", "F (a <-> !b)")
            self.validate_generate_problem(0, "[](a <=> !b)", "G (a <-> !b)")
            self.validate_generate_problem(0, "(a U b)", "(a U b)")
            self.validate_generate_problem(0, "a => () b", "a -> (X b)")
            # length 1
            self.validate_generate_problem(1, "<>(a <=> !b)", "F (a <-> !b)")
            self.validate_generate_problem(1, "[](a <=> !b)", "G (a <-> !b)")
            self.validate_generate_problem(1, "(a U b)", "(a U b)")
            self.validate_generate_problem(1, "a => () b", "a -> (X b)")
            # length 2
            self.validate_generate_problem(2, "<>(a <=> !b)", "F (a <-> !b)")
            self.validate_generate_problem(2, "[](a <=> !b)", "G (a <-> !b)")
            self.validate_generate_problem(2, "(a U b)", "(a U b)")
            self.validate_generate_problem(2, "a => () b", "a -> (X b)")
            # length 3
            self.validate_generate_problem(3, "<>(a <=> !b)", "F (a <-> !b)")
            self.validate_generate_problem(3, "[](a <=> !b)", "G (a <-> !b)")
            self.validate_generate_problem(3, "(a U b)", "(a U b)")
            self.validate_generate_problem(3, "a => () b", "a -> (X b)")
        
    def test_generate_problem_with_fairness(self):
        '''
        This test clearly shows the difference in validating a property with
        or without fairness constraint
        '''
        with tests.Configure(self, __file__, "/philo.smv"):
            # length 0
            # nusmv has fairness always on.
            fml_node= Node.from_ptr(parse_ltl_spec("G (p1.waiting -> F !p1.waiting)"))
            smv     = ltlspec.generate_ltl_problem(self.befsm, fml_node, 0)
            self.assertEqual(SatSolverResult.UNSATISFIABLE, self.satisfiability(smv))
            
            formula = parseLTL("[](p1.waiting => <>!p1.waiting)")
            unfair  = gen.generate_problem(formula, self.befsm, 0, no_fairness=True)
            self.assertEqual(SatSolverResult.UNSATISFIABLE, self.satisfiability(unfair))
            
            fair    = gen.generate_problem(formula, self.befsm, 0, no_fairness=False)
            self.assertEqual(SatSolverResult.UNSATISFIABLE, self.satisfiability(fair))
            
            # length 1
            fml_node= Node.from_ptr(parse_ltl_spec("G (p1.waiting -> F !p1.waiting)"))
            smv     = ltlspec.generate_ltl_problem(self.befsm, fml_node, 1)
            self.assertEqual(SatSolverResult.UNSATISFIABLE, self.satisfiability(smv))
            
            formula = parseLTL("[](p1.waiting => <>!p1.waiting)")
            unfair  = gen.generate_problem(formula, self.befsm, 1, no_fairness=True)
            self.assertEqual(SatSolverResult.SATISFIABLE, self.satisfiability(unfair))
            
            fair    = gen.generate_problem(formula, self.befsm, 1, no_fairness=False)
            self.assertEqual(SatSolverResult.UNSATISFIABLE, self.satisfiability(fair))
            
    def test_generate_problem_with_invars(self):
        '''
        This test clearly shows the difference in validating a property with
        or without fairness constraint
        '''
        with tests.Configure(self, __file__, "/dummy_with_invar.smv"):
            # length 0
            formula = parseLTL("[] v")
            
            noinvar = gen.generate_problem(formula, self.befsm, 0, no_invar=True)
            self.assertEqual(SatSolverResult.SATISFIABLE, self.satisfiability(noinvar))
            
            w_invar = gen.generate_problem(formula, self.befsm, 0, no_invar=False)
            self.assertEqual(SatSolverResult.UNSATISFIABLE, self.satisfiability(w_invar))
            
            # length 1
            noinvar = gen.generate_problem(formula, self.befsm, 1, no_invar=True)
            self.assertEqual(SatSolverResult.SATISFIABLE, self.satisfiability(noinvar))
            
            w_invar = gen.generate_problem(formula, self.befsm, 1, no_invar=False)
            self.assertEqual(SatSolverResult.UNSATISFIABLE, self.satisfiability(w_invar))
            