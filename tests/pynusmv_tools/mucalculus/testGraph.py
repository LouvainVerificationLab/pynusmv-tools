import unittest


from pynusmv_tools.mucalculus.graph import Graph, domaintuple


class TestGraph(unittest.TestCase):
    
    def state_graph1(self):
        s1 = domaintuple(state="s1")
        s2 = domaintuple(state="s2")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        return Graph({s1: frozenset({(stay, s1), (run, s2)}),
                      s2: frozenset({(stay, s2)})})
    
    def state_graph2(self):
        s1 = domaintuple(state="s1")
        s3 = domaintuple(state="s3")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        return Graph({s1: frozenset({(stay, s1), (run, s3)}),
                      s3: frozenset({(stay, s3), (run, s1)})})
    
    def formula_graph(self):
        pq = domaintuple(formula="p & q")
        p = domaintuple(formula="p")
        q = domaintuple(formula="q")
        empty = domaintuple()
        return Graph({pq: frozenset({(empty, p), (empty, q)}),
                      p: frozenset(),
                      q: frozenset()})
    
    def test_union(self):
        states1 = self.state_graph1()
        states2 = self.state_graph2()
        formulas = self.formula_graph()
        
        self.assertEqual(states1, states1.union(states1))
        self.assertEqual(formulas, formulas.union(formulas))
        s1f = {}
        for state in states1.nodes:
            s1f[state] = states1[state]
        for formula in formulas.nodes:
            s1f[formula] = formulas[formula]
        self.assertEqual(states1.union(formulas),
                         Graph(s1f))
        
        s1 = domaintuple(state="s1")
        s2 = domaintuple(state="s2")
        s3 = domaintuple(state="s3")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        self.assertEqual(states1.union(states2),
                         Graph({s1: frozenset({(stay, s1),
                                               (run, s2),
                                               (run, s3)}),
                                s2: frozenset({(stay, s2)}),
                                s3: frozenset({(run, s1),
                                               (stay, s3)})}))
    
    def test_intersection(self):
        states1 = self.state_graph1()
        states2 = self.state_graph2()
        formulas = self.formula_graph()
        
        self.assertEqual(states1, states1.intersection(states1))
        self.assertEqual(formulas, formulas.intersection(formulas))
        self.assertEqual(states1.intersection(formulas),
                         Graph({}))
        
        self.assertEqual(states1.intersection(formulas.union(states1)),
                         states1)
        self.assertEqual(formulas.intersection(formulas.union(states1)),
                         formulas)
        
        s1 = domaintuple(state="s1")
        s2 = domaintuple(state="s2")
        s3 = domaintuple(state="s3")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        self.assertEqual(states1.intersection(states2),
                         Graph({s1: frozenset({(stay, s1)})}))
    
    def test_node_difference(self):
        states1 = self.state_graph1()
        states2 = self.state_graph2()
        formulas = self.formula_graph()
        
        self.assertEqual(Graph({}), states1.node_difference(states1))
        self.assertEqual(Graph({}),
                         formulas.node_difference(formulas))
        self.assertEqual(states1.node_difference(formulas),
                         states1)
        self.assertEqual(formulas.node_difference(states1), formulas)
        
        s1 = domaintuple(state="s1")
        s2 = domaintuple(state="s2")
        s3 = domaintuple(state="s3")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        self.assertEqual(states1.node_difference(states2),
                         Graph({s2: frozenset({(stay, s2)})}))
        self.assertEqual(states2.node_difference(states1),
                         Graph({s3: frozenset({(stay, s3)})}))
    
    def test_edge_difference(self):
        states1 = self.state_graph1()
        states2 = self.state_graph2()
        formulas = self.formula_graph()
        
        self.assertEqual(Graph({node: frozenset() for node in states1}),
                         states1.edge_difference(states1))
        self.assertEqual(Graph({node: frozenset() for node in formulas}),
                         formulas.edge_difference(formulas))
        self.assertEqual(states1.edge_difference(formulas),
                         states1)
        self.assertEqual(formulas.edge_difference(states1), formulas)
        
        s1 = domaintuple(state="s1")
        s2 = domaintuple(state="s2")
        s3 = domaintuple(state="s3")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        self.assertEqual(states1.edge_difference(states2),
                         Graph({s1: frozenset({(run, s2),}),
                                s2: frozenset({(stay, s2)})}))
        self.assertEqual(states2.edge_difference(states1),
                         Graph({s1: frozenset({(run, s3)}),
                                s3: frozenset({(run, s1), (stay, s3)})}))
    
    def test_selection(self):
        states1 = self.state_graph1()
        s1 = domaintuple(state="s1")
        s2 = domaintuple(state="s2")
        s3 = domaintuple(state="s3")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        
        self.assertEqual(states1.selection(node_selector=
                                           lambda n: n.state != "s1"),
                         Graph({s2: frozenset({(stay, s2)})}))
        self.assertEqual(states1.selection(edge_selector=
                                           lambda e: e[1].act == "run"),
                         Graph({s1: frozenset({(run, s2)}),
                                s2: frozenset()}))
        self.assertEqual(states1.selection(node_selector=
                                           lambda n: n.state == "s1",
                                           edge_selector=
                                           lambda e: e[1].act == "run"),
                         Graph({s1: frozenset()}))
    
    def test_join(self):
        states1 = self.state_graph1()
        states2 = self.state_graph2()
        formulas = self.formula_graph()
        
        self.assertEqual(states1.join(states1), states1)
        self.assertEqual(states1.join(states2), states1.intersection(states2))
        
        s1pq = domaintuple(state="s1", formula="p & q")
        s1p = domaintuple(state="s1", formula="p")
        s1q = domaintuple(state="s1", formula="q")
        s2pq = domaintuple(state="s2", formula="p & q")
        s2p = domaintuple(state="s2", formula="p")
        s2q = domaintuple(state="s2", formula="q")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        empty = domaintuple()
        j = Graph({s1pq: frozenset({(stay, s1pq), (stay, s1p), (stay, s1q),
                                    (run, s2pq), (run, s2p), (run, s2q),
                                    (empty, s1p), (empty, s1q)}),
                   s1p: frozenset({(stay, s1p), (run, s2p)}),
                   s1q: frozenset({(stay, s1q), (run, s2q)}),
                   s2pq: frozenset({(stay, s2pq), (stay, s2p), (stay, s2q),
                                    (empty, s2p), (empty, s2q)}),
                   s2p: frozenset({(stay, s2p)}),
                   s2q: frozenset({(stay, s2q)})})
        self.assertEqual(states1.join(formulas), j)
        self.assertEqual(j.join(states1), j)
        self.assertEqual(j.join(formulas), j)
    
    def test_projection(self):
        states1 = self.state_graph1()
        states2 = self.state_graph2()
        formulas = self.formula_graph()
        
        self.assertEqual(states1.projection(node_domain={"state"}), states1)
        self.assertEqual(states1.projection(edge_domain={"act"}), states1)
        self.assertEqual(states1.projection(node_domain={"state"},
                                            edge_domain={"act"}), states1)
        
        s1f = states1.join(formulas)
        s1 = domaintuple(state="s1")
        s2 = domaintuple(state="s2")
        s3 = domaintuple(state="s3")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        self.assertEqual(s1f.projection(node_domain={"state"},
                                        edge_domain={"act"}), states1)
        
        pq = domaintuple(formula="p & q")
        p = domaintuple(formula="p")
        q = domaintuple(formula="q")
        empty = domaintuple()
        self.assertEqual(s1f.projection(node_domain={"formula"},
                                        edge_domain={}),
                         Graph({pq: frozenset(),
                                p: frozenset(),
                                q: frozenset()}))
        self.assertEqual(s1f.projection(node_domain={"formula"}),
                         Graph({pq: frozenset({(stay, pq),
                                               (run, pq),
                                               (run, p),
                                               (run, q),
                                               (stay, p),
                                               (stay, q),
                                               (empty, p),
                                               (empty, q)}),
                                p: frozenset({(stay, p),
                                              (run, p)}),
                                q: frozenset({(stay, q),
                                              (run, q)})}))
    
    def test_extension(self):
        states1 = self.state_graph1()
        s1 = domaintuple(state="s1")
        s11 = domaintuple(state="s1", id=1)
        s2 = domaintuple(state="s2")
        s22 = domaintuple(state="s2", id=2)
        s3 = domaintuple(state="s3")
        stay = domaintuple(act="stay")
        staysure = domaintuple(act="stay", sure=True)
        run = domaintuple(act="run")
        runsure = domaintuple(act="run", sure=True)
        
        self.assertEqual(states1.extension(node_extension=lambda n:
                                           {"id": int(n.state[-1])}),
                         Graph({s11: frozenset({(stay, s11), (run, s22)}),
                                s22: frozenset({(stay, s22)})}))
        self.assertEqual(states1.extension(edge_extension=lambda e:
                                           {"sure": True}),
                         Graph({s1: frozenset({(staysure, s1),
                                               (runsure, s2)}),
                                s2: frozenset({(staysure, s2)})}))
        self.assertEqual(states1.extension(node_extension=lambda n:
                                           {"id": int(n.state[-1])},
                                           edge_extension=lambda e:
                                           {"sure": True}),
                         Graph({s11: frozenset({(staysure, s11),
                                                (runsure, s22)}),
                                s22: frozenset({(staysure, s22)})}))
    
    def test_mapping(self):
        states1 = self.state_graph1()
        s1 = domaintuple(state="s1")
        s1i = domaintuple(id=1)
        s2 = domaintuple(state="s2")
        s2i = domaintuple(id=2)
        s3 = domaintuple(state="s3")
        stay = domaintuple(act="stay")
        run = domaintuple(act="run")
        sure = domaintuple(sure=True)
        
        self.assertEqual(states1.mapping(node_mapping=lambda n:
                                         {"id": int(n.state[-1])}),
                         Graph({s1i: frozenset({(stay, s1i), (run, s2i)}),
                                s2i: frozenset({(stay, s2i)})}))
        self.assertEqual(states1.mapping(edge_mapping=lambda e:
                                         {"sure": True}),
                         Graph({s1: frozenset({(sure, s1), (sure, s2)}),
                                s2: frozenset({(sure, s2)})}))
        self.assertEqual(states1.mapping(node_mapping=lambda n:
                                         {"id": int(n.state[-1])},
                                         edge_mapping=lambda e:
                                         {"sure": True}),
                         Graph({s1i: frozenset({(sure, s1i), (sure, s2i)}),
                                s2i: frozenset({(sure, s2i)})}))
    
    def test_grouping(self):
        states1 = self.state_graph1()
        states2 = self.state_graph2()
        formulas = self.formula_graph()
        
        s1fo = domaintuple(state="s1",
                           formulas=frozenset({domaintuple(formula="p & q"),
                                               domaintuple(formula="p"),
                                               domaintuple(formula="q")}))
        s2fo = domaintuple(state="s2",
                           formulas=frozenset({domaintuple(formula="p & q"),
                                               domaintuple(formula="p"),
                                               domaintuple(formula="q")}))
        stayempty = domaintuple(actions=frozenset({domaintuple(act="stay"),
                                                   domaintuple()}))
        run = domaintuple(actions=frozenset({domaintuple(act="run")}))
        
        s1f = states1.join(formulas)
        g = s1f.grouping(node_group=("formulas", {"state"}),
                         edge_group=("actions", {}))
        self.assertEqual(g, Graph({s1fo: frozenset({(stayempty, s1fo),
                                                    (run, s2fo)}),
                                   s2fo: frozenset({(stayempty, s2fo)})}))
    
    def test_ungrouping(self):
        states1 = self.state_graph1()
        states2 = self.state_graph2()
        formulas = self.formula_graph()
        grouped = states1.join(formulas).grouping(node_group=("formulas",
                                                              {"state"}),
                                                  edge_group=("actions", {}))
        
        s1pq = domaintuple(state="s1", formula="p & q")
        s1p = domaintuple(state="s1", formula="p")
        s1q = domaintuple(state="s1", formula="q")
        s2pq = domaintuple(state="s2", formula="p & q")
        s2p = domaintuple(state="s2", formula="p")
        s2q = domaintuple(state="s2", formula="q")
        s1fo = domaintuple(state="s1",
                           formulas=frozenset({domaintuple(formula="p & q"),
                                               domaintuple(formula="p"),
                                               domaintuple(formula="q")}))
        s2fo = domaintuple(state="s2",
                           formulas=frozenset({domaintuple(formula="p & q"),
                                               domaintuple(formula="p"),
                                               domaintuple(formula="q")}))
        stay = domaintuple(act="stay")
        empty = domaintuple()
        run = domaintuple(act="run")
        stayempty = domaintuple(actions=frozenset({domaintuple(act="stay"),
                                                   domaintuple()}))
        arun = domaintuple(actions=frozenset({domaintuple(act="run")}))
        
        
        ungrouped = grouped.ungrouping(node_group="formulas")
        g = Graph({
                   s1pq: frozenset({(stayempty, s1pq),
                                    (stayempty, s1p),
                                    (stayempty, s1q),
                                    (arun, s2pq),
                                    (arun, s2p),
                                    (arun, s2q)}),
                   s1p: frozenset({(stayempty, s1pq),
                                   (stayempty, s1p),
                                   (stayempty, s1q),
                                   (arun, s2pq),
                                   (arun, s2p),
                                   (arun, s2q)}),
                   s1q: frozenset({(stayempty, s1pq),
                                   (stayempty, s1p),
                                   (stayempty, s1q),
                                   (arun, s2pq),
                                   (arun, s2p),
                                   (arun, s2q)}),
                   s2pq: frozenset({(stayempty, s2pq),
                                    (stayempty, s2p),
                                    (stayempty, s2q)}),
                   s2p: frozenset({(stayempty, s2pq),
                                   (stayempty, s2p),
                                   (stayempty, s2q)}),
                   s2q: frozenset({(stayempty, s2pq),
                                   (stayempty, s2p),
                                   (stayempty, s2q)})
                   })
        self.assertEqual(ungrouped, g)
        
        ungrouped = grouped.ungrouping(edge_group="actions")
        g = Graph({
                   s1fo: frozenset({(stay, s1fo),
                                    (empty, s1fo),
                                    (run, s2fo)}),
                   s2fo: frozenset({(stay, s2fo),
                                    (empty, s2fo)})
                   })
        self.assertEqual(ungrouped, g)
        
        ungrouped = grouped.ungrouping(node_group="formulas",
                                       edge_group="actions")
        g = Graph({
                   s1pq: frozenset({(stay, s1pq),
                                    (stay, s1p),
                                    (stay, s1q),
                                    (empty, s1pq),
                                    (empty, s1p),
                                    (empty, s1q),
                                    (run, s2pq),
                                    (run, s2p),
                                    (run, s2q)}),
                   s1p: frozenset({(stay, s1pq),
                                   (stay, s1p),
                                   (stay, s1q),
                                   (empty, s1pq),
                                   (empty, s1p),
                                   (empty, s1q),
                                   (run, s2pq),
                                   (run, s2p),
                                   (run, s2q)}),
                   s1q: frozenset({(stay, s1pq),
                                   (stay, s1p),
                                   (stay, s1q),
                                   (empty, s1pq),
                                   (empty, s1p),
                                   (empty, s1q),
                                   (run, s2pq),
                                   (run, s2p),
                                   (run, s2q)}),
                   s2pq: frozenset({(stay, s2pq),
                                    (stay, s2p),
                                    (stay, s2q),
                                    (empty, s2pq),
                                    (empty, s2p),
                                    (empty, s2q)}),
                   s2p: frozenset({(stay, s2pq),
                                   (stay, s2p),
                                   (stay, s2q),
                                   (empty, s2pq),
                                   (empty, s2p),
                                   (empty, s2q)}),
                   s2q: frozenset({(stay, s2pq),
                                   (stay, s2p),
                                   (stay, s2q),
                                   (empty, s2pq),
                                   (empty, s2p),
                                   (empty, s2q)})
                   })
        self.assertEqual(ungrouped, g)
    
    def test_ungrouping_not_domaintuple(self):
        states1 = self.state_graph1()
        states2 = self.state_graph2()
        formulas = self.formula_graph()
        grouped = states1.join(formulas).grouping(node_group=("formulas",
                                                              {"state"}),
                                                  edge_group=("actions", {}))
        def list_formulas(node):
            node = dict(node)
            node["formulas"] = frozenset({t.formula for t in node["formulas"]})
            return node
        mapped = grouped.mapping(node_mapping=list_formulas)
        
        s1pq = domaintuple(state="s1", formulas="p & q")
        s1p = domaintuple(state="s1", formulas="p")
        s1q = domaintuple(state="s1", formulas="q")
        s2pq = domaintuple(state="s2", formulas="p & q")
        s2p = domaintuple(state="s2", formulas="p")
        s2q = domaintuple(state="s2", formulas="q")
        stayempty = domaintuple(actions=frozenset({domaintuple(act="stay"),
                                                   domaintuple()}))
        arun = domaintuple(actions=frozenset({domaintuple(act="run")}))
        
        ungrouped = mapped.ungrouping(node_group="formulas")
        g = Graph({
                   s1pq: frozenset({(stayempty, s1pq),
                                    (stayempty, s1p),
                                    (stayempty, s1q),
                                    (arun, s2pq),
                                    (arun, s2p),
                                    (arun, s2q)}),
                   s1p: frozenset({(stayempty, s1pq),
                                   (stayempty, s1p),
                                   (stayempty, s1q),
                                   (arun, s2pq),
                                   (arun, s2p),
                                   (arun, s2q)}),
                   s1q: frozenset({(stayempty, s1pq),
                                   (stayempty, s1p),
                                   (stayempty, s1q),
                                   (arun, s2pq),
                                   (arun, s2p),
                                   (arun, s2q)}),
                   s2pq: frozenset({(stayempty, s2pq),
                                    (stayempty, s2p),
                                    (stayempty, s2q)}),
                   s2p: frozenset({(stayempty, s2pq),
                                   (stayempty, s2p),
                                   (stayempty, s2q)}),
                   s2q: frozenset({(stayempty, s2pq),
                                   (stayempty, s2p),
                                   (stayempty, s2q)})
                   })
        self.assertEqual(ungrouped, g)
    
    def test_ungrouping_not_iterable(self):
        states1 = self.state_graph1()
        ungrouped = states1.ungrouping(node_group="other")
        self.assertEqual(ungrouped, states1)
        
        def state_to_id(node):
            node = dict(node)
            node["state"] = int(node["state"][1:])
            return node
        states1 = states1.mapping(node_mapping=state_to_id)
        self.assertEqual(states1, states1.ungrouping(node_group="state"))