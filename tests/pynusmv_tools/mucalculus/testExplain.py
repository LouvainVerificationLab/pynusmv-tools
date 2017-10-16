import unittest

from functools import reduce

from pynusmv.dd import BDD
from pynusmv.init import init_nusmv, deinit_nusmv
from pynusmv.mc import eval_simple_expression
from pynusmv import model as md

from pynusmv_tools.mucalculus import model
from pynusmv_tools.mucalculus.formula import (MTrue, MFalse, Variable,
                                          Atom, Not, And, Or,
                                          Diamond, Box, Mu, Nu,
                                          alias, SPOI, POI, POD)
from pynusmv_tools.mucalculus import CannotExplainFalseError, hashabledict
from pynusmv_tools.mucalculus.explanation import Obligation
from pynusmv_tools.mucalculus.graph import domaintuple


class TestExplain(unittest.TestCase):
    
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
    
    def cardgame_post_fair(self):
        model.load_from_file("tests/pynusmv_tools/mucalculus/models/"
                             "cardgame-post-fair.smv")
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


    def test_explain_simple(self):
        fsm = self.cardgame()
        
        formulas = [MTrue(), Atom("pcard = Ac")]
        for formula in formulas:
            state = fsm.pick_one_state(formula.eval(fsm))
            expl = formula.explain(fsm, state)
            
            self.assertEqual(len(expl.graph.nodes), 1)
            self.assertEqual(len(set(expl.graph.edges)), 0)
            self.assertEqual(len(expl.unexplained), 0)
            node = next(iter(expl.graph.nodes))
            self.assertEqual(expl.initial, node)
            
            init = Obligation(fsm, state, formula, {})
            #init = dict(init)
            #init.update(initial=True)
            #init = domaintuple(init)
            self.assertEqual(node, init)
        
        with self.assertRaises(CannotExplainFalseError):
            MFalse().explain(fsm, fsm.pick_one_state(fsm.init))


    def test_ex(self):
        fsm = self.cardgame()
    
        expr = Diamond(MTrue())
    
        state = fsm.pick_one_state(fsm.init & expr.eval(fsm))
        expl = expr.explain(fsm, state)
        
        dot = expl.dot()
        self.assertIsNotNone(dot)
        
        init = Obligation(fsm, state, expr, {})
        #init = dict(init)
        #init.update(initial=True)
        #init = domaintuple(init)
        self.assertEqual(expl.initial, init)
        self.assertEqual(len(set(expl.graph.edges)), 1)
        self.assertEqual(next(iter(expl.graph.edges))[0], expl.initial)
        
        succ = next(iter(expl.graph.edges))[2]
        f, s, p, c = succ.fsm, succ.state, succ.formula, succ.context
        self.assertEqual(f, fsm)
        self.assertTrue(s <= fsm.post(fsm.init, transition="time"))
        self.assertEqual(p, MTrue())
        self.assertEqual(c, {})


    def test_ax(self):
        fsm = self.cardgame()
    
        expr = Box(Atom("step = 1"))
    
        state = fsm.pick_one_state(fsm.init & expr.eval(fsm))
        expl = expr.explain(fsm, state)
        
        dot = expl.dot()
        self.assertIsNotNone(dot)
        
        (f, s, p, c) = (expl.initial.fsm, expl.initial.state,
                        expl.initial.formula, expl.initial.context)
    
        self.assertEqual(f, fsm)
        self.assertEqual(s, state)
        self.assertEqual(p, expr)
        self.assertEqual(c, {})
        self.assertTrue(len(list(edge for edge in expl.graph.edges
                                 if edge[0] == expl.initial)) > 0)
        
        for edge in expl.graph.edges:
            if edge[0] == expl.initial:
                succ = edge[2]
                self.assertEqual(succ.fsm, fsm)
                self.assertTrue(succ.state,
                                fsm.post(fsm.init, transition="time"))
                self.assertEqual(succ.formula, Atom("step = 1"))
                self.assertEqual(succ.context, {})
                self.assertEqual(len(list(edge for edge in expl.graph.edges
                                          if edge[0] == succ)), 0)


    def test_ef(self):
        fsm = self.cardgame()
    
        # Compute EF win
        expr = Mu(Variable("Z"),
                  Or(Atom("win"), Diamond(Variable("Z"))))
    
        for state in fsm.pick_all_states(expr.eval(fsm) &
                                         fsm.reachable_states):
            expl = expr.explain(fsm, state)
            self.assertEqual(expl.initial.state, state)
            
            dot = expl.dot()
            self.assertIsNotNone(dot)
            
            e = expl.initial
            while e is not None:
                self.assertEqual(e.fsm, fsm)
                self.assertTrue(e.state <= expr.eval(fsm))
                self.assertEqual(e.context, {})
                
                self.assertTrue(len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) == 1 or
                                len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) <= 0 and
                                e.formula == Atom("win"))
                
                if len(list(edge for edge in expl.graph.edges
                            if edge[0] == e)) > 0:
                    e = next(edge for edge in expl.graph.edges
                             if edge[0] == e)[2]
                else:
                    e = None


    def test_af(self):
        fsm = self.cardgame()
    
        # Compute AF step = 2
        expr = Mu(Variable("Z"),
                  Or(Atom("step = 2"), Box(Variable("Z"))))
    
        for state in fsm.pick_all_states(expr.eval(fsm) &
                                         fsm.reachable_states):
            expl = expr.explain(fsm, state)
            self.assertEqual(expl.initial.state, state)
            
            dot = expl.dot()
            self.assertIsNotNone(dot)
            
            # Follow one path of expl and check that step = 2 is reached
            e = expl.initial
            while e is not None:
                self.assertEqual(e.fsm, fsm)
                self.assertTrue(e.state <= expr.eval(fsm))
                self.assertEqual(e.context, {})
                
                self.assertTrue(len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) > 0 or
                                len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) <= 0 and
                                e.formula == Atom("step = 2"))
                
                if len(list(edge for edge in expl.graph.edges
                            if edge[0] == e)) > 0:
                    e = next(edge for edge in expl.graph.edges
                             if edge[0] == e)[2]
                else:
                    e = None


    def test_eg(self):
        fsm = self.cardgame()
    
        # Compute EG !win
        expr = Nu(Variable("Z"),
                  And(Not(Atom("win")), Diamond(Variable("Z"))))
    
        for state in fsm.pick_all_states(expr.eval(fsm) &
                                         fsm.reachable_states):
            expl = expr.explain(fsm, state)
            self.assertEqual(expl.initial.state, state)
            
            dot = expl.dot()
            self.assertIsNotNone(dot)
            
            # Inspect all nodes
            found = set()
            pending = {expl.initial}
            while len(pending) > 0:
                e = pending.pop()
                found.add(e)
                
                self.assertEqual(e.fsm, fsm)
                self.assertTrue(e.state <= expr.eval(fsm))
                self.assertEqual(e.context, {})
                self.assertTrue(len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) >= 1 or
                                len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) <= 0 and
                                e.formula == Not(Atom("win")))
                
                pending |= {edge[2] for edge in expl.graph.edges
                            if edge[0] == e} - found


    def test_ag(self):
        fsm = self.cardgame()
    
        # Compute AG step <= 4
        expr = Nu(Variable("Z"),
                  And(Atom("step <= 3"), Box(Variable("Z"))))
    
        for state in fsm.pick_all_states(expr.eval(fsm) &
                                         fsm.reachable_states):
            expl = expr.explain(fsm, state)
            self.assertEqual(expl.initial.state, state)
            
            dot = expl.dot()
            self.assertIsNotNone(dot)
            
            # Inspect all nodes
            found = set()
            pending = {expl.initial}
            while len(pending) > 0:
                e = pending.pop()
                found.add(e)
                
                self.assertEqual(e.fsm, fsm)
                self.assertTrue(e.state <= expr.eval(fsm))
                self.assertEqual(e.context, {})
                self.assertTrue(len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) >= 1 or
                                len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) <= 0 and
                                e.formula == Atom("step <= 3"))
                
                pending |= {edge[2] for edge in expl.graph.edges
                            if edge[0] == e} - found
    
    def test_ef_with_alias(self):
        fsm = self.cardgame()
        
        @alias("EX {child}")
        def EX(child):
            return Diamond(child)
        
        @alias()
        def Reach(target):
            return POI(Mu(Variable("Z"), Or(POI(target), EX(Variable("Z")))))
    
        # Compute EF win
        expr = Reach(Atom("win"))
    
        for state in fsm.pick_all_states(expr.eval(fsm) &
                                         fsm.reachable_states):
            expl = expr.explain(fsm, state)
            self.assertEqual(expl.initial.state, state)
            
            self.assertIsNotNone(expl.dot())
            
            e = expl.initial
            while e is not None:
                self.assertEqual(e.fsm, fsm)
                self.assertTrue(e.state <= expr.eval(fsm))
                self.assertEqual(e.context, {})
                
                self.assertTrue(len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) == 1 or
                                len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) <= 0 and
                                e.formula == POI(Atom("win")))
                
                if len(list(edge for edge in expl.graph.edges
                            if edge[0] == e)) > 0:
                    e = next(edge[2] for edge in expl.graph.edges
                             if edge[0] == e)
                else:
                    e = None
    
    def test_eg_with_alias(self):
        fsm = self.cardgame()
        
        @alias("EX {child}")
        def EX(child):
            return Diamond(child)
        
        @alias("EG {inv}")
        def EG(inv):
            return POI(Nu(Variable("Z"),
                       And(POI(inv), EX(Variable("Z")))))
    
        # Compute EG !win
        expr = EG(Not(Atom("win")))
    
        for state in fsm.pick_all_states(expr.eval(fsm) &
                                         fsm.reachable_states):
            expl = expr.explain(fsm, state)
            self.assertEqual(expl.initial.state, state)
            
            self.assertIsNotNone(expl.dot())
            
            # Inspect all nodes
            found = set()
            pending = {expl.initial}
            while len(pending) > 0:
                e = pending.pop()
                found.add(e)
                
                self.assertEqual(e.fsm, fsm)
                self.assertTrue(e.state <= expr.eval(fsm))
                self.assertEqual(e.context, {})
                self.assertTrue(len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) >= 1 or
                                len(list(edge for edge in expl.graph.edges
                                         if edge[0] == e)) <= 0 and
                                e.formula == POI(Not(Atom("win"))))
                
                pending |= {edge[2] for edge in expl.graph.edges
                            if edge[0] == e} - found
    
    def test_ag_with_alias(self):
        fsm = self.cardgame()
        
        @alias("AX {child}")
        def AX(child):
            return Box(child)
            
        @alias("EX {child}")
        def EX(child):
            return Diamond(child)
        
        @EX.negation
        def exneg(child):
            return AX(Not(child))
        @AX.negation
        def axneg(child):
            return EX(Not(child))
        
        @alias("AG {inv}")
        def AG(inv):
            return Nu(Variable("Z"), And(inv, AX(Variable("Z"))))
        
        @alias("EF {target}")
        def EF(target):
            return Mu(Variable("Z"), Or(target, EX(Variable("Z"))))
        
        @AG.negation
        def agneg(inv):
            return EF(Not(inv))
        @EF.negation
        def efneg(target):
            return AG(Not(target))
        
        # Compute AG step <= 1
        expr = AG(Atom("step <= 1"))
        
        nsat = ~expr.eval(fsm)
        self.assertTrue((fsm.init & nsat).isnot_false())
        state = fsm.pick_one_state(nsat & fsm.init)
        self.assertTrue(state <= Not(expr).eval(fsm))
        expl = Not(expr).explain(fsm, state)
        self.assertIsNotNone(expl.dot())
    
    @unittest.skip("Takes too long")
    def test_fair_with_alias(self):
        fsm = self.cardgame_post_fair()
        
        @alias("EX {child}")
        def EX(child):
            return Diamond(child)
        
        @alias()
        def Reach(target):
            return Mu(Variable("W"), Or(target, EX(Variable("W"))))
        
        @alias("And{{{variable} in {elements}}} {body}")
        def BigAnd(body, variable, elements):
            if len(elements) <= 0:
                return MTrue()
            else:
                element = next(iter(elements))
                elembody = body._substitute(variable, element)
                elements = elements[1:]
                if len(elements) > 1:
                    return And(elembody, BigAnd(body, variable, elements))
                elif len(elements) == 1:
                    n = next(iter(elements))
                    nbody = body._substitute(variable, n)
                    return And(elembody, nbody)
                else:
                    return elembody
        
        @alias(form="fair")
        def fair(fsm):
            body = EX(Reach(And(Variable("Z"), Variable("fci"))))
            return Nu(Variable("Z"),
                       BigAnd(body, Variable("fci"),
                              [POI(Variable("fc%d" % index))
                               for index in
                               range(len(fsm.fairness_constraints))]))
        
        # Compute fair
        expr = SPOI(fair(fsm))
        context = {Variable("fc%d" % index): constraint
                   for index, constraint in
                   enumerate(fsm.fairness_constraints)}
        
        sat = expr.eval(fsm, context=context)
        self.assertTrue(fsm.init <= sat)
        state = fsm.pick_one_state(sat & fsm.init)
        expl = expr.explain(fsm, state, context=context)
        self.assertIsNotNone(expl.dot())
    
    def test_simple_fair_with_alias(self):
        class main(md.Module):
            c = md.Var(md.Boolean())
            INIT = c
            TRANS = (c.next() == ~c)
            FAIRNESS = [c, ~c]
            
        model.load(main)
        fsm = model.bddModel()
        self.assertIsNotNone(fsm)
        
        @alias("EX {child}")
        def EX(child):
            return Diamond(child)
        
        @alias()
        def Reach(target):
            return Mu(Variable("W"), Or(target, EX(Variable("W"))))
        
        @alias("And{{{variable} in {elements}}} {body}")
        def BigAnd(body, variable, elements):
            if len(elements) <= 0:
                return MTrue()
            else:
                element = next(iter(elements))
                elembody = body._substitute(variable, element)
                elements = elements[1:]
                if len(elements) > 1:
                    return And(elembody, BigAnd(body, variable, elements))
                elif len(elements) == 1:
                    n = next(iter(elements))
                    nbody = body._substitute(variable, n)
                    return And(elembody, nbody)
                else:
                    return elembody
        
        @alias(form="fair")
        def fair(fsm):
            body = EX(Reach(And(Variable("Z"), Variable("fci"))))
            return Nu(Variable("Z"),
                      BigAnd(body, Variable("fci"),
                             [POI(Variable("fc%d" % index))
                              for index in
                              range(len(fsm.fairness_constraints))]))
        
        # Compute fair
        expr = SPOI(fair(fsm))
        
        context = {Variable("fc%d" % index): constraint
                   for index, constraint in
                   enumerate(fsm.fairness_constraints)}
        sat = expr.eval(fsm, context=context)
        self.assertTrue(fsm.init <= sat)
        state = fsm.pick_one_state(sat & fsm.init)
        
        expl = expr.explain(fsm, state, context=context)
        self.assertIsNotNone(expl.dot())
    
    def test_eg_with_alias_and_pod(self):
        fsm = self.cardgame()
        
        @alias("EX {child}")
        def EX(child):
            return POD(Diamond(child))
        
        @alias("EG {inv}")
        def EG(inv):
            return POI(Nu(Variable("Z"),
                       And(POI(inv), EX(Variable("Z")))))
    
        # Compute EG !win
        expr = EG(Not(Atom("win")))
        state = fsm.pick_one_state(expr.eval(fsm) & fsm.init)
        expl = expr.explain(fsm, state)
        self.assertIsNotNone(expl.dot())