'''
This module validates the behavior of the utility functions defined in the 
module :mod:`pynusmv_tools.bmcLTL.check`.
'''

from unittest             import TestCase
from tests                import utils as tests

from pynusmv_tools.bmcLTL.parsing import parseLTL
from pynusmv_tools.bmcLTL         import check # the tested module 

class TestCheck(TestCase):
    
    def test_GLOBALLY_check_ltl_onepb(self):
        with tests.Configure(self, __file__, "/example.smv"):
            formula      = parseLTL("[](a <=> !b)")
            for k in range(10):
                status,trace = check.check_ltl_onepb(formula, k)
                self.assertEqual("Ok", status)
                self.assertIsNone(trace)
             
            # already violated in the initial state
            formula      = parseLTL("[](a <=> b)")
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Violation", status)
            self.assertIsNotNone(trace)
            self.assertEqual(0, len(trace))
                     
                 
    def test_EVENTUALLY_check_ltl_onepb(self):
        with tests.Configure(self, __file__, "/example.smv"):       
            # proving a violation of this prop necessitates at least two
            # steps: flip --> flop --> flip 
            formula      = parseLTL("<>(a <=> b)")
             
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            status,trace = check.check_ltl_onepb(formula, 1)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            # a loop is identified
            status,trace = check.check_ltl_onepb(formula, 2)
            self.assertEqual("Violation", status)
            self.assertIsNotNone(trace)
            self.assertEqual(2, len(trace))
             
            # valid in the initial state (hence for any bound)
            formula      = parseLTL("<>(a | b)")
            for k in range(10):
                status,trace = check.check_ltl_onepb(formula, k)
                self.assertEqual("Ok", status)
                self.assertIsNone(trace)
                     
    def test_NEXT_check_ltl_onepb(self):
        with tests.Configure(self, __file__, "/example.smv"):       
            # false in the initial state
            formula      = parseLTL("() a")
             
            # however the violation is not detected when no move is allowed
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            status,trace = check.check_ltl_onepb(formula, 1)
            self.assertEqual("Violation", status)
            self.assertIsNotNone(trace)
            self.assertEqual(1, len(trace))
             
            # true in the initial state
            formula      = parseLTL("()() a")
            # not reachable
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
            # not quite yet
            status,trace = check.check_ltl_onepb(formula, 1)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
            # ok
            status,trace = check.check_ltl_onepb(formula, 2)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
            # and even for longer traces
            status,trace = check.check_ltl_onepb(formula, 3)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
                 
    def test_WEAKUNTIL_check_ltl_onepb(self):
        with tests.Configure(self, __file__, "/never_b.smv"):
            # entailed by the automaton
            formula      = parseLTL("a W b")
             
            # not reachable
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
            # already looping but no counter example
            status,trace = check.check_ltl_onepb(formula, 1)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            # true in the initial state
            formula      = parseLTL("b W a")
             
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            status,trace = check.check_ltl_onepb(formula, 1)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            status,trace = check.check_ltl_onepb(formula, 2)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            status,trace = check.check_ltl_onepb(formula, 3)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            # violated right away
            formula      = parseLTL("b W !a")
             
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Violation", status)
            self.assertIsNotNone(trace)
            self.assertEqual(0, len(trace))
                 
    def test_UNTIL_check_ltl_onepb(self):
        with tests.Configure(self, __file__, "/never_b.smv"):    
            # entailed by the automaton
            formula      = parseLTL("a U b")
             
            # not reachable
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            # this is where U differs from W: at infinity, b must hold
            status,trace = check.check_ltl_onepb(formula, 1)
            self.assertEqual("Violation", status)
            self.assertIsNotNone(trace)
            self.assertEqual(1, len(trace))
             
            # true in the initial state
            formula      = parseLTL("b U a")
             
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            status,trace = check.check_ltl_onepb(formula, 1)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            status,trace = check.check_ltl_onepb(formula, 2)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            status,trace = check.check_ltl_onepb(formula, 3)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
             
            # violated right away
            formula      = parseLTL("b U !a")
             
            status,trace = check.check_ltl_onepb(formula, 0)
            self.assertEqual("Violation", status)
            self.assertIsNotNone(trace)
            self.assertEqual(0, len(trace))
                 
    def test_GLOBALLY_check_ltl(self):
        with tests.Configure(self, __file__, "/example.smv"):
            status,l,trace = check.check_ltl(parseLTL("[](a <=> !b)"), 5)
            self.assertEqual('Ok', status)
            self.assertEqual(5, l)
            self.assertIsNone(trace)
             
            status,l,trace = check.check_ltl(parseLTL("[](a & b)"), 5)
            self.assertEqual('Violation', status)
            self.assertEqual(0, l)
            self.assertIsNotNone(trace)
                 
    def test_EVENTUALLY_check_ltl(self):
        with tests.Configure(self, __file__, "/example.smv"):
            status,l,trace = check.check_ltl(parseLTL("<>(a <=> !b)"), 5)
            self.assertEqual('Ok', status)
            self.assertEqual(5, l)
            self.assertIsNone(trace)
             
            status,l,trace = check.check_ltl(parseLTL("<>(a & b)"), 5)
            self.assertEqual('Violation', status)
            self.assertEqual(2, l)
            self.assertIsNotNone(trace)
                 
    def test_NEXT_check_ltl(self):
        with tests.Configure(self, __file__, "/example.smv"):
            status,l,trace = check.check_ltl(parseLTL("()() a"), 5)
            self.assertEqual('Ok', status)
            self.assertEqual(5, l)
            self.assertIsNone(trace)
             
            status,l,trace = check.check_ltl(parseLTL("() a"), 5)
            self.assertEqual('Violation', status)
            self.assertEqual(1, l)
            self.assertIsNotNone(trace)
                 
    def test_WEAKUNTIL_check_ltl(self):
        with tests.Configure(self, __file__, "/never_b.smv"):
            status,l,trace = check.check_ltl(parseLTL("a W b"), 5)
            self.assertEqual('Ok', status)
            self.assertEqual(5, l)
            self.assertIsNone(trace)
             
            status,l,trace = check.check_ltl(parseLTL("b W a"), 5)
            self.assertEqual('Ok', status)
            self.assertEqual(5, l)
            self.assertIsNone(trace)
             
            status,l,trace = check.check_ltl(parseLTL("b W !a"), 5)
            self.assertEqual('Violation', status)
            self.assertEqual(0, l)
            self.assertIsNotNone(trace)
                 
    def test_UNTIL_check_ltl(self):
        with tests.Configure(self, __file__, "/never_b.smv"):
            status,l,trace = check.check_ltl(parseLTL("b U a"), 5)
            self.assertEqual('Ok', status)
            self.assertEqual(5, l)
            self.assertIsNone(trace)
             
            status,l,trace = check.check_ltl(parseLTL("a U b"), 5)
            self.assertEqual('Violation', status)
            self.assertEqual(1, l)
            self.assertIsNotNone(trace)
             
            status,l,trace = check.check_ltl(parseLTL("b W !a"), 5)
            self.assertEqual('Violation', status)
            self.assertEqual(0, l)
            self.assertIsNotNone(trace)
                
    def test_check_ltl_fairness(self):
        """
        This tests validates two features::
            1. the use of a non-variable symbol in the formula
            2. the use of the fairness flag when performing the check.
        """
        with tests.Configure(self, __file__, "/philo.smv"):
            # no one must wait forever:
            # -> this is entailed by fair execution but not in general
            formula = parseLTL("(!<>[](p1.waiting)) & (!<>[](p2.waiting))")
            
            # unfair
            status,_,trace = check.check_ltl(formula, 10, no_fairness=True)
            self.assertEqual("Violation", status)
            self.assertEqual(3, len(trace))
            
            # fair exec only
            status,_,trace = check.check_ltl(formula, 10, no_fairness=False)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
            
    def test_check_ltl_invariants(self):
        """
        This tests the use of the invariants flag when performing the check.
        """
        with tests.Configure(self, __file__, "/dummy_with_invar.smv"):
            formula = parseLTL("[] v")
            
            # invariants enforced
            status,_,trace = check.check_ltl(formula, 10, no_invar=True)
            self.assertEqual("Violation", status)
            self.assertEqual(0, len(trace))
            
            # invariants enforced
            status,_,trace = check.check_ltl(formula, 10, no_invar=False)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
            
    def test_check_ltl_arithmetics(self):
        """
        This tests the use of the invariants flag when performing the check.
        """
        with tests.Configure(self, __file__, "/numbers.smv"):
            formula = parseLTL("[] a < 7")
            
            status,_,trace = check.check_ltl(formula, 10, no_invar=False)
            self.assertEqual("Ok", status)
            self.assertIsNone(trace)
            