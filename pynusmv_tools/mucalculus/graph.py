"""
Relational Graph Algebra
Inspired from "Model Checking and Evidence Exploration",
by Y. Dong, C.R. Ramakrishnan, S.A. Smolka
(refered as [MCEE] in the sequel)

A domain is either a primitive domain (integers, reals, etc.)
or a Cartesian product of domains D_1, ..., D_n. [MCEE]

A relational graph is a directed graph <V, E> where vertices V are elements
of the node domain D_V and edges E are elements of V x D_E x V, where D_E
is the edge domain. [MCEE]

The basic operators are [MCEE]:
 * the union of two graphs defined on the same node and edge domains;
 * the intersection of two graphs defined on the same node and edge domains;
 * the node difference of two graphs defined on the same node and edge
   domains;
 * the edge difference of two graphs defined on the same node and edge
   domains;
 * the selection of a part of a graph based on two boolean functions for
   selecting nodes and edges, respectively;
 * the projection of a graph on two node and edge sub-domains;
 * the Cartesian product of two graphs.


In terms of implementation, a Graph has a set of nodes and a set of edges, that
is, a set of triplets where the first and third elements are nodes and the
second element is the edge value.

Nodes and edge values must be domaintuples. The domain of a node or edge is
the set of keys of the corresponding domaintuple. Domaintuples values MUST
be hashable.

Nodes and edges do not have to share the same domains, as in [MCEE]; instead,
the full domain of nodes and edges is the union of all the keys of the
domaintuples of nodes and edges, respectively.
"""

from collections import Mapping, defaultdict

class domaintuple(Mapping):
    """
    A domaintuple is a read-only dictionary where missing keys default to None.
    getitem will thus never fails and will return None if the key is not
    present; keys and items are only the ones where the value is note None.
    At construction, all None values are removed from the initializing values
    such that only non-None values are kept.

    Domaintuples values MUST be hashable.

    Inspired from frozendict from https://pypi.python.org/pypi/frozendict/.
    """

    def __init__(self, *args, **kwargs):
        self.__dict = {k: v
                       for k, v in dict(*args, **kwargs).items()
                       if v is not None}
        self.__hash = None

    def __getitem__(self, key):
        try:
            return self.__dict[key]
        except KeyError:
            return None
    
    def __getattr__(self, name):
        if name in self.__dict:
            return self.__dict[name]
        else:
            return None

    def copy(self):
        return domaintuple(self)

    def __iter__(self):
        return iter(self.__dict)

    def __len__(self):
        return len(self.__dict)

    def __repr__(self):
        return '<domaintuple %s>' % repr(self.__dict)

    def __hash__(self):
        if self.__hash is None:
            self.__hash = hash(frozenset(self.__dict.items()))
        return self.__hash

    def keys(self):
        return self.__dict.keys()

    def values(self):
        return self.__dict.values()

    def items(self):
        return self.__dict.items()

    def __contains__(self, key):
        return key in self.__dict

    def get(self, key, default=None):
        return self.__dict.get(key, default=default)

    def __eq__(self, other):
        return self.__dict == other

    def __ne__(self, other):
        return self.__dict != other


class Graph(Mapping):
    """
    A relational graph.
    
    A graph is represented by a mapping, giving, for each node, the set of
    pairs of edge value and successing node. This set of pairs must be a
    frozenset and each pair must be a tuple.
    
    A constraint any graph must fulfill is that each node appearing as a
    successor must also appear as a key of the mapping (even if its set of
    successing nodes is empty).
    """
    
    def __init__(self, *args, **kwargs):
        """
        Create a new relational graph. Its arguments must initialize the
        mapping corresponding to the graph.
        """
        self.__dict = dict(*args, **kwargs)
        assert(self.check())
    
    @property
    def nodes(self):
        return self.__dict.keys()
    
    @property
    def edges(self):
        for node, successors in self.items():
            for edge, successor in successors:
                yield (node, edge, successor)
    
    def check(self):
        """
        Check whether this graph respects the constraints of graphs:
         * each key is a domaintuple
         * each value is a frozenset of pairs of domaintuples
         * each successor is a key of this graph
        """
        for node, successors in self.items():
            if not isinstance(node, domaintuple):
                return False
            if not isinstance(successors, frozenset):
                return False
            for edge, successor in successors:
                if not isinstance(edge, domaintuple):
                    return False
                if not isinstance(successor, domaintuple):
                    return False
                if successor not in self:
                    return False
        return True
    
    def __getitem__(self, key):
        return self.__dict[key]

    def copy(self):
        return Graph(self)

    def __iter__(self):
        return iter(self.__dict)

    def __len__(self):
        return len(self.__dict)

    def __repr__(self):
        return '<Graph %s>' % repr(self.__dict)

    def union(self, other):
        """
        Compute the union of this graph and other.

        other -- another Graph.

        Return a new Graph representing the union of self and other.
        """
        new_graph = defaultdict(frozenset, self)
        for node, successors in other.items():
            new_graph[node] |= successors
        return Graph(new_graph)

    __or__ = union

    def intersection(self, other):
        """
        Compute the intersection of this graph and other.

        other -- another Graph.

        Return a new Graph representing the intersection of self and other.
        """
        new_graph = {node: frozenset({(edge, successor)
                                      for edge, successor in successors
                                      if (edge, successor) in other[node]})
                     for node, successors in self.items()
                     if node in other}
        return Graph(new_graph)

    __and__ = intersection

    def node_difference(self, other):
        """
        Compute the node difference of this graph and other.

        other -- another Graph.

        Return a new Graph representing the node difference of self and other.
        """
        new_graph = {node: frozenset({(edge, successor)
                                      for edge, successor in successors
                                      if successor not in other})
                     for node, successors in self.items()
                     if node not in other}
        return Graph(new_graph)

    def edge_difference(self, other):
        """
        Compute the edge difference of this graph and other.

        other -- another Graph.

        Return a new Graph representing the edge difference of self and other.
        """
        new_graph = {node: frozenset({(edge, successor)
                                      for edge, successor in successors
                                      if node not in other or
                                         (edge, successor) not in other[node]})
                     for node, successors in self.items()}
        return Graph(new_graph)

    def selection(self, node_selector=None, edge_selector=None):
        """
        Compute the selection of this graph according to node_selector and
        edge_selector.

        node_selector -- a function taking a node as argument and returning
                         whether or not it is selected or not;
        edge_selector -- a function taking an edge as argument and
                         returning whether or not it is selected or not.

        If node_selector is None, all nodes are kept; if edge_selector is None,
        all edges for which the extremities are kept, are kept.

        Return a new Graph where nodes are all nodes of this graph for which
        node_selector returns a true value, and where edges are all edges of
        this graph for which edge_selector returns a true value.
        """
        if node_selector is None:
            nodes = set(self.nodes)
        else:
            nodes = {node for node in self if node_selector(node)}
        new_graph = {node: frozenset({(edge, successor)
                                      for edge, successor in successors
                                      if successor in nodes and
                                         (edge_selector is None or
                                          edge_selector((node,
                                                         edge,
                                                         successor)))})
                     for node, successors in self.items()
                     if node in nodes}
        return Graph(new_graph)

    def projection(self, node_domain=None, edge_domain=None):
        """
        Compute the projection of this graph on the given node and edge
        domains.

        node_domain -- a sub-domain of the node domain of this graph, that is,
                       a set of domain names;
        edge_domain -- a sub-domain of the edge domain of this graph, that is,
                       a set of domain names.

        If node_domain is None, nodes are kept as they are; if edge_domain is
        None, edge values are kept as they are.

        Return a new Graph where nodes are new domaintuples with keys of
        node_domain and edges are new domaintuples with keys of edge_domain.
        Edges without non-None values are removed if edge_domain is given.
        """
        if node_domain is None:
            nodes = {node: node for node in self.nodes}
            new_graph = {node: set() for node in nodes}
        else:
            nodes = {node: self.project(node, node_domain)
                     for node in self.nodes}
            new_graph = {node: set() for node in nodes.values()}
        if edge_domain is None:
            for origin, edge, end in self.edges:
                new_graph[nodes[origin]].add((edge, nodes[end]))
        else:
            for origin, edge, end in self.edges:
                projected = self.project(edge, edge_domain)
                if projected:
                    new_graph[nodes[origin]].add((projected, nodes[end]))
        return Graph({node: frozenset(successors)
                      for node, successors in new_graph.items()})

    def join(self, other):
        """
        Compute the join of this graph with other.

        other -- another Graph.

        Return a new Graph where the node set is the join of this graph
        nodes and the other graph nodes, that is, each node of this graph
        is joined with each node of the other graph for which the common
        domains have the same value,
        and each edge embeds at least one edge from this graph or the other
        graph, and keeps the remaining idle (None values), that is,
        the resulting edge values are each edge value of this graph with None
        values for the domains of the other graph and vice versa, plus the
        joined edge values, that is, the edge values that agree on common
        domains.
        """
        new_graph = {}
        nodes = {}
        # A dictionary of pairs of nodes telling whether they agree on common
        # domains
        agree = {}
        for node1 in self.nodes:
            for node2 in other.nodes:
                if (node1, node2) not in agree:
                    agree[(node1, node2)] = all(node1[key] == node2[key]
                                                for key in node1.keys() &
                                                           node2.keys())
                if agree[(node1, node2)]:
                    nodes[(node1, node2)] = self.join_elements(node1, node2)
                    new_graph[nodes[(node1, node2)]] = set()

        for origin1, edge1, end1 in self.edges:
            for origin2, edge2, end2 in other.edges:
                if (agree[(origin1, origin2)] and
                    agree[(end1, end2)]):
                    if (edge1, edge2) not in agree:
                        agree[(edge1, edge2)] = all(edge1[key] == edge2[key]
                                                    for key in edge1.keys() &
                                                               edge2.keys())
                    if agree[(edge1, edge2)]:
                        new_graph[nodes[(origin1, origin2)]].add(
                            (self.join_elements(edge1, edge2),
                             nodes[(end1, end2)]))
        for origin1, edge1, end1 in self.edges:
            for node2 in other.nodes:
                if (agree[(origin1, node2)] and
                    agree[(end1, node2)]):
                    new_graph[nodes[(origin1, node2)]].add(
                        (edge1, nodes[(end1, node2)]))
        for node1 in self.nodes:
            for origin2, edge2, end2 in other.edges:
                if (agree[(node1, origin2)] and
                    agree[(node1, end2)]):
                    new_graph[nodes[(node1, origin2)]].add(
                        (edge2, nodes[(node1, end2)]))
        return Graph({node: frozenset(successors)
                      for node, successors in new_graph.items()})

    def extension(self, node_extension=None, edge_extension=None):
        """
        Extend each node with node_extension and each edge value with
        edge_extension.

        node_extension -- a function taking a node as argument and returning
                          new domain values for this node;
        edge_extension -- a function taking an edge (origin, edge value, end)
                          as argument and returning new domain values for this
                          edge.

        If node_extension is None, nodes are kept as they are;
        if edge_extension is None, edges are kept as they are.

        node_extension and edge_extension can return new values for sub-domains
        for which nodes and edges are already defined and the new values will
        replace the old ones.
        """
        new_graph = {}
        if node_extension is not None:
            nodes = {}
            for node in self.nodes:
                nodes[node] = self.extend(node, node_extension(node))
                new_graph[nodes[node]] = set()
        else:
            nodes = {node: node for node in self.nodes}
            new_graph = {node: set() for node in self.nodes}

        for origin, edge, end in self.edges:
            if edge_extension is not None:
                new_graph[nodes[origin]].add(
                    (self.extend(edge, edge_extension((origin, edge, end))),
                     nodes[end]))
            else:
                new_graph[nodes[origin]].add((domaintuple(edge), nodes[end]))

        return Graph({node: frozenset(successors)
                      for node, successors in new_graph.items()})

    def mapping(self, node_mapping=None, edge_mapping=None):
        """
        Map each node to node_mapping and each edge value to edge_mapping.

        node_mapping -- a function taking a node as argument and returning the
                        corresponding new node;
        edge_mapping -- a function taking an edge as argument (origin,
                        edge value, end) and returning the corresponding edge
                        value.

        If node_mapping is None, all nodes are kept as they are;
        if edge_mapping is None, all edge values are kept as they are.
        """
        if node_mapping is not None:
            nodes = {node: domaintuple(node_mapping(node))
                     for node in self.nodes}
            new_graph = {node: set() for node in nodes.values()}
        else:
            nodes = {node: node for node in self.nodes}
            new_graph = {node: set() for node in nodes}
        for origin, edge, end in self.edges:
            if edge_mapping is not None:
                new_edge = domaintuple(edge_mapping((origin, edge, end)))
            else:
                new_edge = edge
            new_graph[nodes[origin]].add((new_edge, nodes[end]))
        return Graph({node: frozenset(successors)
                      for node, successors in new_graph.items()})

    def grouping(self, node_group=None, edge_group=None):
        """
        Group all nodes with the same values for domains in the given node
        domains and accumulate domains outside the given domains into
        a new domain named with the given name;
        all edges between two grouped nodes are grouped according to the same
        rules.

        node_group -- a couple where the first element is the name for the new
                      domain in which the groups are given and the second
                      element is the set of domain names used for grouping;
        edge_group -- a couple where the first element is the name for the new
                      domain in which the groups are given and the second
                      element is the set of domain names used for grouping.

        If node_group is None, no grouping is made on nodes; if edge_group is
        None, no grouping is made on edge values.
        """
        if node_group is not None:
            node_group_name, node_domains = node_group
            grouped_nodes = defaultdict(lambda: set())
            for node in self.nodes:
                grouped_nodes[self.project(node, node_domains)].add(node)
            nodes = {}
            for projected in grouped_nodes:
                inner = frozenset(self.project(n, n.keys() - node_domains)
                                  for n in grouped_nodes[projected])
                grouped_node = self.extend(projected, {node_group_name: inner})
                for node in grouped_nodes[projected]:
                    nodes[node] = grouped_node
        else:
            nodes = {node: node for node in self.nodes}

        new_graph = {node: set() for node in nodes.values()}

        if edge_group is not None:
            edge_group_name, edge_domains = edge_group
            grouped_edges = defaultdict(lambda: set())
            for origin, edge, end in self.edges:
                grouped_edges[(nodes[origin],
                               self.project(edge, edge_domains),
                               nodes[end])].add(edge)
            edges = set()
            for origin, projected, end in grouped_edges:
                inner = frozenset(self.project(e, e.keys() - edge_domains)
                                  for e in grouped_edges[(origin,
                                                          projected,
                                                          end)])
                grouped_edge = self.extend(projected, {edge_group_name: inner})
                edges.add((origin, grouped_edge, end))
        else:
            edges = {(nodes[origin], edge, nodes[end])
                     for origin, edge, end in self.edges}
        for origin, edge, end in edges:
            new_graph[origin].add((edge, end))
        return Graph({node: frozenset(successors)
                      for node, successors in new_graph.items()})

    def ungrouping(self, node_group=None, edge_group=None):
        """
        Ungroup all nodes and edges based on the given domains.
        Duplicate each node and edge and replace the value of node_group (and
        edge_group, respectively) by each value it contains; if the value of
        node_group (or edge_group) is not iterable, it is kept as it is.

        node_group -- if not None, the name of a domain of nodes;
        edge_group -- if not None, the name of a domain of edges.

        If node_group is None, no ungrouping is made on nodes; if edge_group is
        None, no ungrouping is made on edges.
        """
        if node_group is None:
            nodes = {node: {node} for node in self.nodes}
        else:
            nodes = {node: self.ungroup(node, node_group)
                     for node in self.nodes}
        new_graph = {}
        for node, successors in self.items():
            for new_node in nodes[node]:
                new_graph[new_node] = set()
                for edge, successor in successors:
                    for new_edge in ({edge} if edge_group is None
                                     else self.ungroup(edge, edge_group)):
                        for new_succ in nodes[successor]:
                            new_graph[new_node].add((new_edge, new_succ))
        return Graph({node: frozenset(successors)
                      for node, successors in new_graph.items()})

    def dot(self):
        """
        Return a dot representation of this graph.

        The nodes and edges of the returned dot graph are labelled with their
        domain values (as "key = value"), sorted alphabetically.

        If a node or edge value has a domain named "dot", its value is used
        as the style of the corresponding node or edge.
        """
        ids = {}
        dot = "digraph {\n"

        nodes = []
        for nid, node in enumerate(self.nodes):
            ids[node] = nid
            if "dot" in node:
                style = node["dot"]
            else:
                label = "\n".join(str(key) + " = " + str(value)
                                  for key, value in sorted(node.items()))
                style = 'label="%s"' % label
            nodes.append('s%d [%s]' % (ids[node], style))
        dot += "\n".join(nodes) + "\n"

        edges = []
        for origin, edge, end in self.edges:
            if "dot" in edge:
                style = edge["dot"]
            else:
                label = "\n".join(str(key) + " = " + str(value)
                                  for key, value in sorted(edge.items()))
                style = 'label="%s"' % label
            edges.append('s%d -> s%d [%s]' %
                         (ids[origin], ids[end], style))
        dot += "\n".join(edges)

        dot += "\n}"
        return dot

    @staticmethod
    def ungroup(element, domain):
        """
        Ungroup domain value of element into new domaintuples for each value of
        domain.
        That is, for each value of domain in element, a new domaintuple is
        created, sharing the same other values as element, and getting only one
        of the values of domain in element as domain.
        If the value of domain in element is an iterable of domaintuples, the
        domains of these tuples are flattened in element instead of getting one
        new value containing the whole domaintuple.
        
        element -- a domaintuple;
        domain -- a domain of element.
        
        If the value of domain in element is not iterable, it is kept as it is
        and element is returned.
        The returned value is the set of new elements, even if domain in
        element is not iterable (in this case, the returned set contains only
        one element).
        """
        new_elements = set()
        try:
            for value in element[domain]:
                if isinstance(value, domaintuple):
                    old = dict(element)
                    del old[domain]
                    old.update(value)
                    new_elements.add(domaintuple(old))
                else:
                    new_elements.add(Graph.extend(element, {domain: value}))
        except TypeError:
            new_elements = {element}
        return new_elements

    @staticmethod
    def group(element, elements, domain, group_name):
        """
        Return the grouped domaintuple of all elements sharing the same domain
        values as element.

        element -- a domaintuple;
        elements -- a set of domaintuple;
        domain -- a sub-domain of element's domain.
        
        Return a domaintuple where domains in the given sub-domain are the same
        as element, and where the sub-domain outside the given sub-domain
        is the accumulation of all the other domaintuples in elements sharing
        the same value as element in the given sub-domain.
        """
        outer = dict(Graph.project(element, domain))
        inner = set()
        for other in elements:
            if Graph.project(other, domain) == outer:
                inner.add(Graph.project(other, other.keys() - domain))
        outer.update({group_name: frozenset(inner)})
        return domaintuple(outer)

    @staticmethod
    def project(element, domain):
        """
        Return the projection of the given element on the given domain.

        element -- a domaintuple;
        domain -- a subset of element keys.

        Return a new domaintuple where keys are the elements of domain and
        values are the corresponding values in element.
        """
        return domaintuple({k: v for k, v in element.items()
                                 if k in domain})

    @staticmethod
    def join_elements(element1, element2):
        """
        Return the join of the two elements.

        element1 -- a domaintuple;
        element2 -- another domaintuple; agrees on domains common with
                    element1.

        Return a new domaintuple with all the keys of element1 and element2,
        and the corresponding values in the corresponding elements
        (note that common keys agree).
        """
        element = dict(element1)
        element.update(element2)
        return domaintuple(element)

    @staticmethod
    def extend(old, new):
        """
        Return the extension of old with new.

        old -- a domaintuple;
        new -- another domaintuple; defined on a disjoint domain.

        Return a new domaintuple defined on the union of domains of old and new
        and agreeing with the corresponding domaintuples on their respective
        domains.
        """
        old = dict(old)
        old.update(new)
        return domaintuple(old)