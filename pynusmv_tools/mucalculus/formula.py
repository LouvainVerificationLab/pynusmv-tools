import inspect
from collections import defaultdict
from functools import cmp_to_key

from pynusmv.dd import BDD
from pynusmv.mc import eval_simple_expression

from . import (UnknownVariableError, CannotExplainFalseError,
               ExclusiveChoiceError)
from . import hashabledict, orderedset
from .graph import domaintuple, Graph
from .explanation import Obligation, Explanation

__all__ = ['MTrue', 'MFalse', 'Atom', 'Variable', 'Not', 'And', 'Or',
           'Diamond', 'Box', 'Mu', 'Nu',
           'alias', 'pretty_format',
           'SPOI', 'POI', 'SPOD', 'POD',
           'attributor', 'obligation_attributor', 'edge_attributor',
           'chooser']

# ----- FORMULAS --------------------------------------------------------------

class Formula:
    """
    An asbract mu-calculus formula.
    """
    
    def __init__(self, generator=None, arguments=None, markers=None,
                 attributors=None, choosers=None):
        """
        Create a new formula aliased by generator where arguments are the
        arguments of the generator to obtain this formula. The formula is
        marked by markers and will generate attributes to obligations and
        edges from attributors. The obligations labelled by the formula will
        be given to choosers for choosing the sucessors.
        
        generator -- if not None, an _Aliaser;
        arguments -- if not None, a dictionary of generator argument names ->
                     actual values for the corresponding alias.
        markers -- the set of markers of the created formula.
        attributors -- if not None, a list of attributors.
        choosers -- if not None, a list of choosers.
        
        If generator is not None, arguments keys should correspond to its
        arguments. If generator is not None, this formula should be equal to
        generator(**arguments).
        
        Should be extended by subclasses.
        """
        
        self.generator = generator
        if arguments is not None:
            self.arguments = hashabledict(arguments)
        else:
            self.arguments = hashabledict()
        self._substitutions = {}
        
        if markers is None:
            markers = set()
        self.markers = markers
        
        if attributors is None:
            attributors = []
        self.attributors = attributors
        
        if choosers is None:
            choosers = []
        self.choosers = choosers
    
    def __getattr__(self, name):
        if name in self.arguments:
            return self.arguments[name]
        else:
            raise AttributeError(name + " is not an attribute of " + str(self))
    
    def __deepcopy__(self, memo):
        return self._copy()
    
    def eval(self, fsm, context=None, cache={}):
        """
        Evaluate this formula on fsm in context. Return the BDD
        representing the set of states computed by this formula on
        fsm in context.
        
        fsm -- the system on which evaluate this expression;
        context -- a dictionary of variable name -> BDD pairs representing the
                   context in which evaluate this formula;
        cache -- the cache to avoid recomputation.
        """
        if context is None:
            context = {}
        hashable_context = frozenset(context.items())
        key = (self, fsm, hashable_context)
        if key not in cache:
            cache[key] = self._eval(fsm, context)
        return cache[key]
    
    def _eval(self, fsm, context=None):
        """
        Evaluate this formula on fsm in context. Return the BDD
        representing the set of states computed by this formula on
        fsm in context.
        
        fsm -- the system on which evaluate this expression;
        context -- a dictionary of variable name -> BDD pairs representing the
                   context in which evaluate this formula.
        """
        raise NotImplementedError("Should be implemented by subclasses.")
    
    def explain(self, fsm, state, context=None, attributors=None,
                choosers=None, expand=None):
        """
        Return an explanation explaining why state belongs to the evaluation of
        this formula in context. If expand is not None, expand is an
        Explanation; in this case, expand the given Explanation by explaining
        why state belongs to the evaluation of this formula in context.
        
        If attributors are given, these attributors are called after calling
        formulas attributors.
        
        If choosers are given, they are called after calling formula choosers.
        
        fsm -- the system;
        state -- the state, must belong to the evaluation of this formula
                 on fsm in context;
        context -- the context in which state belongs to this formula
                   evaluation.
        attributors -- if not None, a list of attributors; attributors must
                       return hashable values for all attributes they provide.
        choosers -- if not None, a list of choosers; these choosers must take
                    an obligation, a set of choices and a type of choice as
                    arguments, and return a subset of these choices.
        expand -- if not None, an Explanation that will be expanded.
        """
        attributors = attributors if attributors is not None else []
        attr = []
        for attributor in attributors:
            if isinstance(attributor, _Attributorer):
                attr.extend(attributor.attributors)
            else:
                attr.append(attributor)
        attributors = attr
        
        choosers = choosers if choosers is not None else []
        chsers = []
        for chooser in choosers:
            if isinstance(chooser, _Chooserer):
                chsers.append(chooser.chooser)
            else:
                chsers.append(chooser)
        choosers = chsers
        
        context = (hashabledict(context)
                   if context is not None else hashabledict())
        
        initial = Obligation(fsm, state, self, context)
        if expand is not None:
            nodes = {Graph.project(node,
                                   {"state", "fsm",
                                    "formula", "context"}): node
                     for node in expand.untranslated.nodes}
            visited = orderedset(nodes.keys())
        else:
            nodes = {}
            visited = orderedset()
        pending = orderedset({initial})
        unexplained = set()
        transitions = orderedset()
        
        while len(pending) > 0:
            current = pending.pop()
            (fsm, state, formula, context) = (current.fsm, current.state,
                                              current.formula, current.context)
            # Keep points of decision unexplained
            # except initial if expand is given (we want to explain this one!)
            if ((POD in formula.markers or SPOD in formula.markers) and
                (current != initial or expand is None)):
                unexplained.add(current)
            else:
                current_choosers = formula.choosers + choosers
                if len(current_choosers):
                    # The question above does not apply to these cases.
                    obligations, type_ = formula._choices(fsm, state, context)
                    choices = obligations
                    
                    # If a chooser returns None, ignore it and keep the
                    # previous result
                    chosen = False
                    for chooser in current_choosers:
                        new_obligations = chooser(current, obligations, type_)
                        if new_obligations is not None:
                            obligations = new_obligations
                            chosen = True
                    
                    # If no chooser made a choice (all None), backtrack and
                    # use _explain
                    if not chosen:
                        obligations = formula._explain(fsm, state, context)
                    
                    else:
                        # If type_ is exclusive and more than one choice is
                        # done, this is an error
                        if type_ == "exclusive" and len(obligations) > 1:
                            raise ExclusiveChoiceError("Choosers chose more"
                                                       " than one obligation"
                                                       " from the exclusive"
                                                       " choices for " +
                                                       str(current))
                        
                        # The obligation stays (partially) unexplained
                        # if choice is empty or type_ is inclusive and not all
                        # choices were made
                        if (len(obligations) <= 0 or
                            (type_ == "inclusive" and obligations != choices)):
                            unexplained.add(current)
                else:
                    obligations = formula._explain(fsm, state, context)
                transitions |= ((current, obligation)
                                for obligation in obligations)
                pending |= obligations - visited
            visited.add(current)
        
        new_nodes = visited - nodes.keys()
        
        # Apply attributors
        for obligation in new_nodes:
                node = dict(obligation)
                ## Attribute unexplained and initial nodes
                #if obligation in unexplained:
                #    node["unexplained"] = True
                #if not expand and obligation == initial:
                #    node["initial"] = True
                for attributor in obligation.formula.attributors + attributors:
                    if isinstance(attributor, _ObligationAttributor):
                        node.update(attributor(node))
                nodes[obligation] = domaintuple(node)
        edges = set()
        for origin, end in transitions:
            edge = dict()
            for attributor in origin.formula.attributors + attributors:
                if isinstance(attributor, _EdgeAttributor):
                    edge.update(attributor((nodes[origin], edge, nodes[end])))
            edges.add((nodes[origin], domaintuple(edge), nodes[end]))
        
        # Expand the untranslated explanation if needed
        untranslated = {node: set() for node in nodes.values()}
        for origin, edge, end in edges:
            untranslated[origin].add((edge, end))
        untranslated = Graph({node: frozenset(successors)
                              for node, successors in untranslated.items()})
        if expand is not None:
            untranslated = untranslated.union(expand.untranslated)
            if initial in unexplained:
                unexplained = (expand.unexplained |
                               {nodes[unexpl] for unexpl in unexplained})
            else:
                unexplained = ((expand.unexplained |
                                {nodes[unexpl] for unexpl in unexplained}) -
                               {nodes[initial]})
            initial = expand.initial
        else:
            unexplained = {nodes[obligation] for obligation in unexplained}
            initial = nodes[initial]
        
        # Translate bits of the explanation
        if expand is not None:
            graph = expand.graph
            translated = expand.translated
        else:
            graph = Graph({})
            translated = set()
        # Add newly created nodes and edges to translated graph
        newly_created = defaultdict(set,
                                    {nodes[new_node]: set()
                                     for new_node in new_nodes})
        for origin, edge, end in edges:
            newly_created[origin].add((edge, end))
            if end not in newly_created:
                newly_created[end] = set()
        graph = graph.union(Graph({node: frozenset(successors)
                                   for node, successors
                                   in newly_created.items()}))
        
        # Extract from untranslated the set of translatable nodes
        # (not translated yet)
        translatable = {node for node in untranslated.nodes
                             if node.formula and
                                node.formula.generator and
                                node.formula.generator.translator and
                                node not in translated}
        
        # Get fully explained subgraphs
        subgraphs = {}
        for node in translatable:
            subgraph, frontier = self._get_sub_explanation(untranslated, node)
            # The subgraph is fully explained if
            # the only unexplained nodes are at the frontier
            if not ((subgraph.nodes & unexplained) - frontier):
                subgraphs[node] = subgraph
        
        # Sort translatable nodes
        def cmp_subgraphs(node1, node2):
            if subgraphs[node1].nodes < subgraphs[node2].nodes:
                return -1
            elif subgraphs[node1].nodes > subgraphs[node2].nodes:
                return 1
            else:
                return 0
        to_translate = sorted(subgraphs.keys(), key=cmp_to_key(cmp_subgraphs))
        
        # Translate translatable nodes and add corresponding sub-graphs
        # in graph
        for node in to_translate:
            # Extract subgraph from graph
            subgraph, _ = self._get_sub_explanation(graph, node)
            # Translate subgraph
            translated_sub = node.formula.generator.translator(subgraph, node)
            # Add translated subgraph in graph
            graph = graph.union(translated_sub)
            # Add translated node to translated set
            translated.add(node)
        
        return Explanation(graph, initial, unexplained, translated,
                           untranslated)
    
    def _get_sub_explanation(self, graph, node):
        """
        Given a node of graph with a formula attribute with a generator,
        return the sub-graph corresponding to the part the generator generated.
        This is achieved by considering that the boundaries of the generated
        formula are given by its Formula arguments.
        Also return the frontier, that is, the nodes that are given by its
        Formula arguments.
        
        graph -- a graph;
        node -- a node of graph, containing a formula attribute with a
                generator.
        """
        nodes = set()
        edges = set()
        pending = {node}
        subformulas = {arg for arg in node.formula.arguments.values()
                       if isinstance(arg, Formula)}
        frontier = set()
        new_graph = {}
        
        while pending:
            current = pending.pop()
            new_graph[current] = set()
            if current.formula not in subformulas:
                for edge, next in graph[current]:
                    new_graph[current].add((edge, next))
                    edges.add((current, edge, next))
                    if next not in nodes:
                        pending.add(next)
            else:
                frontier.add(current)
        
        return (Graph({node: frozenset(successors)
                       for node, successors in new_graph.items()}), frontier)
    
    def _explain(self, fsm, state, context):
        """
        Return the set of obligations needed to explain why state of fsm
        satifies this formula under context.
        
        fsm -- the fsm of state;
        state -- a state of fsm satisfying self in context;
        context -- a dictionary of variable -> BDDs containing at least
                   all free variables of self.
        """
        raise NotImplementedError("Should be implemented by subclasses.")
    
    def _choices(self, fsm, state, context):
        """
        Return the set of choices a user can make to explain why state of
        fsm satisfies this formula in context.
        
        The returned value is a couple where the first element is the set of
        possible choices and the second element is whether the choice should
        be "exclusive" (at most one element of the set) or "inclusive" (any
        subset of the set), or there is not choice to make ("none").
        
        Note that a choice is fully performed if it is exclusive and exactly
        one element of the set is used, or if it is inclusive and all elements
        of the set are used.
        
        fsm -- the system;
        state -- the state, must belong to the evaluation of this formula
                 on fsm in context;
        context -- the context in which state belongs to this formula
                   evaluation.
        """
        raise NotImplementedError("Should be implemented by subclasses.")
    
    def __str__(self, noform=None):
        if self.generator is None or self.generator.form is None:
            return noform
        else:
            return self.generator.form.format(**self.arguments)
    
    def __repr__(self):
        return str(self)
    
    def _copy(self):
        """
        Return of copy of this formula.
        """
        raise NotImplementedError("Should be implemented by subclasses.")
    
    def _negate(self, negated):
        """
        Return the negator of this formula.
        """
        if self.generator is None or self.generator.negator is None:
            return negated
        else:
            return self.generator.negator(**self.arguments)
    
    def _substitute(self, variable, other, substitution=None):
        """
        Return a copy of this formula where all occurrences of variable
        are replaced by other.
        
        variable -- a Variable;
        other -- a Formula;
        substitution -- the substitution if this formula is not aliased
                        or the substitution breaks the alias.
        
        This method should be implemented by subclasses and call this method
        with the additional substiution argument.
        """
        if (variable, other) in self._substitutions:
            return self._substitutions[(variable, other)]
        
        if self.generator is not None:
            args = {name: arg._substitute(variable, other)
                    for name, arg in self.arguments.items()
                    if isinstance(arg, Formula)}
            args.update({name: arg
                         for name, arg in self.arguments.items()
                         if not isinstance(arg, Formula)})
            gen_sub = self.generator(**args)
            
            gen_sub.markers = self.markers.copy()
            gen_sub.attributors = self.attributors.copy()
            
            if gen_sub == substitution:
                self._substitutions[(variable, other)] = gen_sub
                return gen_sub
        self._substitutions[(variable, other)] = substitution
        return substitution


class MTrue(Formula):
    """
    The true formula.
    """
    
    def _eval(self, fsm, context=None):
        return BDD.true(fsm.bddEnc.DDmanager)
    
    def _explain(self, fsm, state, context):
        # The Explanation needs no successor to explain True
        return set()
    
    def _choices(self, fsm, state, context):
        return (self._explain(fsm, state, context), "none")
    
    def __str__(self):
        return super(MTrue, self).__str__("true")
    
    def _no_alias(self):
        return "true"
    
    def __eq__(self, other):
        return type(other) is MTrue
    
    def __hash__(self):
        return hash("true")
    
    def _copy(self):
        cp = MTrue(generator=self.generator, arguments=self.arguments,
                   markers=self.markers.copy(),
                   attributors=self.attributors.copy(),
                   choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = MFalse(markers=self.markers.copy(),
                         attributors=self.attributors.copy(),
                         choosers=self.choosers.copy())
        return super(MTrue, self)._negate(negated)
    
    def _substitute(self, variable, other):
        self_sub = MTrue(markers=self.markers.copy(),
                         attributors=self.attributors.copy(),
                         choosers=self.choosers.copy())
        return super(MTrue, self)._substitute(variable, other,
                                              substitution=self_sub)


class MFalse(Formula):
    """
    The false formula.
    """
    
    def _eval(self, fsm, context=None):
        return BDD.false(fsm.bddEnc.DDmanager)
    
    def _explain(self, fsm, state, context):
        raise CannotExplainFalseError("Cannot explain why state "
                                      "belongs to false.")
    
    def _choices(self, fsm, state, context):
        raise CannotExplainFalseError("Cannot explain why state "
                                      "belongs to false.")
    
    def __str__(self):
        return super(MFalse, self).__str__("false")
    
    def _no_alias(self):
        return "false"
    
    def __eq__(self, other):
        return type(other) is MFalse
    
    def __hash__(self):
        return hash("false")
    
    def _copy(self):
        cp = MFalse(generator=self.generator, arguments=self.arguments,
                    markers=self.markers.copy(),
                    attributors=self.attributors.copy(),
                    choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = MTrue(markers=self.markers.copy(),
                        attributors=self.attributors.copy(),
                        choosers=self.choosers.copy())
        return super(MFalse, self)._negate(negated)
    
    def _substitute(self, variable, other):
        self_sub = MFalse(markers=self.markers.copy(),
                          attributors=self.attributors.copy(),
                          choosers=self.choosers.copy())
        return super(MFalse, self)._substitute(variable, other,
                                               substitution=self_sub)


class Atom(Formula):
    """
    An atomic proposition.
    """
    
    def __init__(self, expression,
                 generator=None, arguments=None,
                 markers=None,
                 attributors=None,
                 choosers=None):
        """
        Initialize an atomic proposition with expression.
        
        expression -- the expression of the proposition, as a string.
        """
        super(Atom, self).__init__(generator=generator, arguments=arguments,
                                   markers=markers,
                                   attributors=attributors,
                                   choosers=choosers)
        self.expression = expression
    
    def _eval(self, fsm, context=None):
        return eval_simple_expression(fsm, self.expression)
    
    def _explain(self, fsm, state, context):
        # The Explanation needs no successor to explain Atom
        return set()
    
    def _choices(self, fsm, state, context):
        return (self._explain(fsm, state, context), "none")
    
    def __str__(self):
        s = self.expression
        return super(Atom, self).__str__(s)
    
    def _no_alias(self):
        return self.expression
    
    def __eq__(self, other):
        if type(other) is not Atom:
            return False
        else:
            return self.expression == other.expression
    
    def __hash__(self):
        return 17 + 23 * hash("Atom") + 23 * 23 * hash(self.expression)
    
    def _copy(self):
        cp = Atom(self.expression,
                  generator=self.generator, arguments=self.arguments,
                  markers=self.markers.copy(),
                  attributors=self.attributors.copy(),
                  choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = Not(self._copy(), markers=self.markers.copy(),
                      attributors=self.attributors.copy(),
                      choosers=self.choosers.copy())
        return super(Atom, self)._negate(negated)
    
    def _substitute(self, variable, other):
        self_sub = Atom(self.expression, markers=self.markers.copy(),
                        attributors=self.attributors.copy(),
                        choosers=self.choosers.copy())
        return super(Atom, self)._substitute(variable, other,
                                             substitution=self_sub)


class Variable(Formula):
    """
    A variable.
    """
    
    def __init__(self, name,
                 generator=None, arguments=None,
                 markers=None,
                 attributors=None,
                 choosers=None):
        """
        Initialize a variable with name.
        
        name -- the name of the variable, as a string.
        """
        super(Variable, self).__init__(generator=generator,
                                       arguments=arguments,
                                       markers=markers,
                                       attributors=attributors,
                                       choosers=choosers)
        self.name = name
    
    def _eval(self, fsm, context=None):
        if context is None or self not in context:
            raise UnknownVariableError("Variable " + self.name + " not in "
                                       "context.")
        return context[self]
    
    def _explain(self, fsm, state, context):
        # The Explanation needs no successor to explain Variable
        return set()
    
    def _choices(self, fsm, state, context):
        return (self._explain(fsm, state, context), "none")
    
    def __str__(self):
        return super(Variable, self).__str__(self.name)
    
    def _no_alias(self):
        return self.name
    
    def __eq__(self, other):
        if type(other) is not Variable:
            return False
        else:
            return self.name == other.name
    
    def __hash__(self):
        return 17 + 23 * hash("Variable") + 23 * 23 * hash(self.name)
    
    def _copy(self):
        cp = Variable(self.name,
                      generator=self.generator, arguments=self.arguments,
                      markers=self.markers.copy(),
                      attributors=self.attributors.copy(),
                      choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = Not(self._copy(), markers=self.markers.copy(),
                      attributors=self.attributors.copy(),
                      choosers=self.choosers.copy())
        return super(Variable, self)._negate(negated)
    
    def _substitute(self, variable, other):
        if variable == self:
            return other
        else:
            self_sub = Variable(self.name, markers=self.markers.copy(),
                                attributors=self.attributors.copy(),
                                choosers=self.choosers.copy())
            return super(Variable, self)._substitute(variable, other,
                                                     substitution=self_sub)
    
    def __lt__(self, other):
        if not isinstance(other, Variable):
            raise TypeError("unorderable types: Variable(), " + type(other))
        else:
            return self.name < other.name


class Not(Formula):
    """
    The negation operator.
    """
    
    def __init__(self, child,
                 generator=None, arguments=None,
                 markers=None,
                 attributors=None,
                 choosers=None):
        """
        Initialize a negator formula with child.
        
        child -- the child of the formula.
        """
        super(Not, self).__init__(generator=generator, arguments=arguments,
                                  markers=markers,
                                  attributors=attributors,
                                  choosers=choosers)
        self.child = child
    
    def _eval(self, fsm, context=None):
        return ~self.child.eval(fsm, context)
    
    def _explain(self, fsm, state, context):
        if isinstance(self.child, Atom) or isinstance(self.child, Variable):
            # The Explanation needs no successor to explain ~Atom or ~Variable
            return set()
        else:
            # Translate into positive normal form
            return {Obligation(fsm, state, self.child._negate(), context)}
    
    def _choices(self, fsm, state, context):
        return (self._explain(fsm, state, context), "none")
    
    def __str__(self):
        return super(Not, self).__str__("~" + str(self.child))
    
    def _no_alias(self):
        return "~" + self.child._no_alias()
    
    def __eq__(self, other):
        if type(other) is not Not:
            return False
        else:
            return self.child == other.child
    
    def __hash__(self):
        return 17 + 23 * hash("Not") + 23 * 23 * hash(self.child)
    
    def _copy(self):
        cp = Not(self.child._copy(),
                 generator=self.generator, arguments=self.arguments,
                 markers=self.markers.copy(),
                 attributors=self.attributors.copy(),
                 choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = self.child._copy()
        return super(Not, self)._negate(negated)
    
    def _substitute(self, variable, other):
        self_sub = Not(self.child._substitute(variable, other),
                       markers=self.markers.copy(),
                       attributors=self.attributors.copy(),
                       choosers=self.choosers.copy())
        return super(Not, self)._substitute(variable, other,
                                            substitution=self_sub)


class And(Formula):
    """
    The conjunction operator.
    """
    
    def __init__(self, left, right,
                 generator=None, arguments=None,
                 markers=None,
                 attributors=None,
                 choosers=None):
        """
        Initialize a conjunction formula with left and right.
        
        left -- the left child of the formula;
        right -- the right childf of the formula.
        """
        super(And, self).__init__(generator=generator, arguments=arguments,
                                  markers=markers,
                                  attributors=attributors,
                                  choosers=choosers)
        self.left = left
        self.right = right
    
    def _eval(self, fsm, context=None):
        return (self.left.eval(fsm, context) & self.right.eval(fsm, context))
    
    def _explain(self, fsm, state, context):
        return {Obligation(fsm, state, self.left, context),
                Obligation(fsm, state, self.right, context)}
    
    def _choices(self, fsm, state, context):
        return (self._explain(fsm, state, context), "inclusive")
    
    def __str__(self):
        s = "(" + str(self.left) + " & " + str(self.right) + ")"
        return super(And, self).__str__(s)
    
    def _no_alias(self):
        return ("(" + self.left._no_alias() + " & " + self.right._no_alias() +
                ")")
    
    def __eq__(self, other):
        if type(other) is not And:
            return False
        else:
            return ((self.left == other.left and self.right == other.right) or
                    (self.left == other.right and self.right == other.left))
    
    def __hash__(self):
        return (17 + 23 * hash("And") +
                23 * 23 * (hash(self.left) + hash(self.right)))
    
    def _copy(self):
        cp = And(self.left._copy(), self.right._copy(),
                 generator=self.generator, arguments=self.arguments,
                 markers=self.markers.copy(),
                 attributors=self.attributors.copy(),
                 choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = Or(self.left._negate(), self.right._negate(),
                     markers=self.markers.copy(),
                     attributors=self.attributors.copy(),
                     choosers=self.choosers.copy())
        return super(And, self)._negate(negated)
    
    def _substitute(self, variable, other):
        self_sub = And(self.left._substitute(variable, other),
                       self.right._substitute(variable, other),
                       markers=self.markers.copy(),
                       attributors=self.attributors.copy(),
                       choosers=self.choosers.copy())
        return super(And, self)._substitute(variable, other,
                                            substitution=self_sub)


class Or(Formula):
    """
    The disjunction operator.
    """
    
    def __init__(self, left, right,
                 generator=None, arguments=None,
                 markers=None,
                 attributors=None,
                 choosers=None):
        """
        Initialize a disjunction formula with left and right.
        
        left -- the left child of the formula;
        right -- the right childf of the formula.
        """
        super(Or, self).__init__(generator=generator, arguments=arguments,
                                 markers=markers,
                                 attributors=attributors,
                                 choosers=choosers)
        self.left = left
        self.right = right
    
    def _eval(self, fsm, context=None):
        return (self.left.eval(fsm, context) | self.right.eval(fsm, context))
    
    def _explain(self, fsm, state, context):
        if state <= self.left.eval(fsm, context):
            return {Obligation(fsm, state, self.left, context)}
        else:
            return {Obligation(fsm, state, self.right, context)}
    
    def _choices(self, fsm, state, context):
        choices = set()
        if state <= self.left.eval(fsm, context):
            choices.add(Obligation(fsm, state, self.left, context))
        if state <= self.right.eval(fsm, context):
            choices.add(Obligation(fsm, state, self.right, context))
        return (choices, "exclusive")
    
    def __str__(self):
        s = "(" + str(self.left) + " | " + str(self.right) + ")"
        return super(Or, self).__str__(s)
    
    def _no_alias(self):
        return ("(" + self.left._no_alias() + " | " + self.right._no_alias() +
                ")")
    
    def __eq__(self, other):
        if type(other) is not Or:
            return False
        else:
            return ((self.left == other.left and self.right == other.right) or
                    (self.left == other.right and self.right == other.left))
    
    def __hash__(self):
        return (17 + 23 * hash("Or") +
                23 * 23 * (hash(self.left) + hash(self.right)))
    
    def _copy(self):
        cp = Or(self.left._copy(), self.right._copy(),
                generator=self.generator, arguments=self.arguments,
                markers=self.markers.copy(),
                attributors=self.attributors.copy(),
                choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = And(self.left._negate(), self.right._negate(),
                      markers=self.markers.copy(),
                      attributors=self.attributors.copy(),
                      choosers=self.choosers.copy())
        return super(Or, self)._negate(negated)
    
    def _substitute(self, variable, other):
        self_sub = Or(self.left._substitute(variable, other),
                      self.right._substitute(variable, other),
                      markers=self.markers.copy(),
                      attributors=self.attributors.copy(),
                      choosers=self.choosers.copy())
        return super(Or, self)._substitute(variable, other,
                                           substitution=self_sub)


class Diamond(Formula):
    """
    The diamond operator.
    
    Diamond operators are evaluated on transition relations of models.
    The possible transition relations are defined by the values of
    the "transition" input variable of the model.
    """
    
    def __init__(self, child, transition="time", inputs=None,
                 generator=None, arguments=None,
                 markers=None,
                 attributors=None,
                 choosers=None):
        """
        Initialize a diamond formula with child through transition relation.
        
        child -- the child of the formula.
        transition -- the name of the transition relation, as a string.
        inputs -- if not None, a simple expression over inputs variables of
                  the transition relation.
        """
        super(Diamond, self).__init__(generator=generator, arguments=arguments,
                                      markers=markers,
                                      attributors=attributors,
                                      choosers=choosers)
        self.transition = transition
        self.inputs = inputs
        self.child = child
        
        # Add default attributor: relation name and inputs if exist
        _keep_transition_and_inputs(self)
    
    def _eval(self, fsm, context=None):
        if self.inputs is not None:
            inputs = eval_simple_expression(fsm, self.inputs)
        else:
            inputs = BDD.true(fsm)
        return fsm.pre(self.child.eval(fsm, context),
                       transition=self.transition,
                       inputs=inputs)
    
    def _explain(self, fsm, state, context):
        if self.inputs is not None:
            inputs = eval_simple_expression(fsm, self.inputs)
        else:
            inputs = BDD.true(fsm)
        next = fsm.pick_one_state(fsm.post(state, transition=self.transition,
                                           inputs=inputs)
                                  & self.child.eval(fsm, context))
        return {Obligation(fsm, next, self.child, context)}
    
    def _choices(self, fsm, state, context):
        if self.inputs is not None:
            inputs = eval_simple_expression(fsm, self.inputs)
        else:
            inputs = BDD.true(fsm)
        nexts = (fsm.post(state, transition=self.transition, inputs=inputs) &
                 self.child.eval(fsm, context))
        choices = {Obligation(fsm, n, self.child, context)
                   for n in fsm.pick_all_states(nexts)}
        return (choices, "exclusive")
    
    def __str__(self):
        if self.inputs is not None:
            transition = str(self.transition) + " : " + str(self.inputs)
        else:
            transition = str(self.transition)
        s = "<" + transition + ">" + str(self.child)
        return super(Diamond, self).__str__(s)
    
    def _no_alias(self):
        if self.inputs is not None:
            transition = str(self.transition) + " : " + str(self.inputs)
        else:
            transition = str(self.transition)
        return "<" + transition + ">" + self.child._no_alias()
    
    def __eq__(self, other):
        if type(other) is not Diamond:
            return False
        else:
            return (self.transition == other.transition and
                    self.inputs == other.inputs and
                    self.child == other.child)
    
    def __hash__(self):
        return (17 + 23 * hash("Diamond") +
                23 * 23 * hash(self.transition) + 
                23 * 23 * 23 * hash(self.inputs) +
                23 * 23 * 23 * 23 * hash(self.child))
    
    def _copy(self):
        cp = Diamond(self.child._copy(), transition=self.transition,
                     inputs=self.inputs,
                     generator=self.generator, arguments=self.arguments,
                     markers=self.markers.copy(),
                     attributors=self.attributors.copy(),
                     choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = Box(self.child._negate(), transition=self.transition,
                      inputs=self.inputs,
                      markers=self.markers.copy(),
                      attributors=self.attributors.copy(),
                      choosers=self.choosers.copy())
        return super(Diamond, self)._negate(negated)
    
    def _substitute(self, variable, other):
        self_sub = Diamond(self.child._substitute(variable, other),
                           transition=self.transition,
                           inputs=self.inputs,
                           markers=self.markers.copy(),
                           attributors=self.attributors.copy(),
                           choosers=self.choosers.copy())
        return super(Diamond, self)._substitute(variable, other,
                                                substitution=self_sub)


class Box(Formula):
    """
    The box operator.
    
    Box operators are evaluated on transition relations of models. The possible
    transition relations are defined by the values of the "transition"
    input variable of the model.
    """
    
    def __init__(self, child, transition="time", inputs=None,
                 generator=None, arguments=None,
                 markers=None,
                 attributors=None,
                 choosers=None):
        """
        Initialize a box formula with child through transition relation.
        
        child -- the child of the formula.
        transition -- the name of the transition relation, as a string.
        inputs -- if not None, a simple expression over inputs variables of
                  the transition relation.
        """
        super(Box, self).__init__(generator=generator, arguments=arguments,
                                  markers=markers,
                                  attributors=attributors,
                                  choosers=choosers)
        self.transition = transition
        self.inputs = inputs
        self.child = child
        
        # Add default attributor: relation name and inputs if exist
        _keep_transition_and_inputs(self)
    
    def _eval(self, fsm, context=None):
        if self.inputs is not None:
            inputs = eval_simple_expression(fsm, self.inputs)
        else:
            inputs = BDD.true(fsm)
        return ~fsm.pre(~self.child.eval(fsm, context),
                        transition=self.transition,
                        inputs=inputs)
    
    def _explain(self, fsm, state, context):
        if self.inputs is not None:
            inputs = eval_simple_expression(fsm, self.inputs)
        else:
            inputs = BDD.true(fsm)
        obligations = {Obligation(fsm, n, self.child, context)
                       for n in fsm.pick_all_states(
                                fsm.post(state, transition=self.transition,
                                         inputs=inputs))}
        return obligations
    
    def _choices(self, fsm, state, context):
        if self.inputs is not None:
            inputs = eval_simple_expression(fsm, self.inputs)
        else:
            inputs = BDD.true(fsm)
        choices = {Obligation(fsm, n, self.child, context)
                   for n in fsm.pick_all_states(
                            fsm.post(state, transition=self.transition,
                                     inputs=inputs))}
        return (choices, "inclusive")
    
    def __str__(self):
        if self.inputs is not None:
            transition = str(self.transition) + " : " + str(self.inputs)
        else:
            transition = str(self.transition)
        s = "[" + transition + "]" + str(self.child)
        return super(Box, self).__str__(s)
    
    def _no_alias(self):
        if self.inputs is not None:
            transition = str(self.transition) + " : " + str(self.inputs)
        else:
            transition = str(self.transition)
        return "[" + transition + "]" + self.child._no_alias()
    
    def __eq__(self, other):
        if type(other) is not Box:
            return False
        else:
            return (self.transition == other.transition and
                    self.inputs == other.inputs and
                    self.child == other.child)
    
    def __hash__(self):
        return (17 + 23 * hash("Box") +
                23 * 23 * hash(self.transition) +
                23 * 23 * 23 * hash(self.inputs) +
                23 * 23 * 23 * 23 * hash(self.child))
    
    def _copy(self):
        cp = Box(self.child._copy(), transition=self.transition,
                 inputs=self.inputs,
                 generator=self.generator, arguments=self.arguments,
                 markers=self.markers.copy(),
                 attributors=self.attributors.copy(),
                 choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = Diamond(self.child._negate(), transition=self.transition,
                          inputs=self.inputs,
                          markers=self.markers.copy(),
                          attributors=self.attributors.copy(),
                          choosers=self.choosers.copy())
        return super(Box, self)._negate(negated)
    
    def _substitute(self, variable, other):
        self_sub = Box(self.child._substitute(variable, other),
                       transition=self.transition,
                       inputs=self.inputs,
                       markers=self.markers.copy(),
                       attributors=self.attributors.copy(),
                       choosers=self.choosers.copy())
        return super(Box, self)._substitute(variable, other,
                                            substitution=self_sub)


class Mu(Formula):
    """
    The least fixpoint operator.
    """
    
    def __init__(self, variable, child, shortcut=None,
                 generator=None, arguments=None,
                 markers=None,
                 attributors=None,
                 choosers=None):
        """
        Initialize a least fixpoint formula with child, on variable.
        
        variable -- the variable name of the variable child depends on.
        child -- the child of the formula.
        """
        super(Mu, self).__init__(generator=generator, arguments=arguments,
                                 markers=markers,
                                 attributors=attributors,
                                 choosers=choosers)
        self.variable = variable
        self.child = child
    
    def _eval(self, fsm, context=None):
        if context is None:
            context = {}
        else:
            context = dict(context)
        
        context[self.variable] = BDD.false(fsm.bddEnc.DDmanager)

        old = context[self.variable]
        new = self.child.eval(fsm, context)
        
        while old != new:
            old = new
            context[self.variable] = old
            new = self.child.eval(fsm, context)
        
        return new
    
    def _explain(self, fsm, state, context):
        if context is None:
            context = dict()
        oldcontext = context
        context = dict(context)
        
        if self.generator is not None and self.generator.bounded is not None:
            @alias(form=self.generator.bounded)
            def shortcut(variable, body, bound, **kwargs):
                if bound <= 0:
                    return MFalse()
                elif bound <= 1:
                    return body._substitute(variable, MFalse())
                #elif bound <= 2:
                #    return body._substitute(variable,
                #                            body._substitute(variable,
                #                                             MFalse()))
                else:
                    return body._substitute(variable, shortcut(variable, body,
                                                               bound-1,
                                                               **kwargs))
        else:
            @alias("({body})^{bound}({variable}=False)")
            def shortcut(variable, body, bound, **kwargs):
                if bound <= 0:
                    return MFalse()
                elif bound <= 1:
                    return body._substitute(variable, MFalse())
                elif bound <= 2:
                    return body._substitute(variable,
                                            body._substitute(variable,
                                                             MFalse()))
                else:
                    return body._substitute(variable, shortcut(variable, body,
                                                               bound-1,
                                                               **kwargs))
        
        context[self.variable] = BDD.false(fsm.bddEnc.DDmanager)
        old = context[self.variable]
        chi = MFalse()
        
        bound = 0
        while not (state <= old):
            chi = self.child._substitute(self.variable, chi)
            old = chi.eval(fsm, context)
            bound += 1
        
        return {Obligation(fsm, state, shortcut(self.variable, self.child,
                                                bound, **self.arguments),
                           oldcontext)}
    
    def _choices(self, fsm, state, context):
        return (self._explain(fsm, state, context), "none")
    
    def __str__(self):
        s = "mu " + str(self.variable) + "." + str(self.child)
        return super(Mu, self).__str__(s)
    
    def _no_alias(self):
        return "mu " + str(self.variable) + "." + self.child._no_alias()
    
    def __eq__(self, other):
        if type(other) is not Mu:
            return False
        else:
            return (self.variable == other.variable and
                    self.child == other.child)
    
    def __hash__(self):
        return (17 + 23 * hash("Mu") +
                23 * 23 * hash(self.variable) + 
                23 * 23 * 23 * hash(self.child))
    
    def _copy(self):
        cp = Mu(self.variable._copy(), self.child._copy(),
                generator=self.generator, arguments=self.arguments,
                markers=self.markers.copy(),
                attributors=self.attributors.copy(),
                choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = Nu(self.variable._copy(),
                     self.child._substitute(self.variable,
                                            Not(self.variable))._negate(),
                     markers=self.markers.copy(),
                     attributors=self.attributors.copy(),
                     choosers=self.choosers.copy())
        return super(Mu, self)._negate(negated)
    
    def _substitute(self, variable, other):
        if self.variable == variable:
            # New scope for variable, do not substitute further
            return self._copy()
        else:
            self_sub = Mu(self.variable._copy(),
                          self.child._substitute(variable, other),
                          markers=self.markers.copy(),
                          attributors=self.attributors.copy(),
                          choosers=self.choosers.copy())
            return super(Mu, self)._substitute(variable, other,
                                               substitution=self_sub)


class Nu(Formula):
    """
    The greatest fixpoint operator.
    """
    
    def __init__(self, variable, child,
                 generator=None, arguments=None,
                 markers=None,
                 attributors=None,
                 choosers=None):
        """
        Initialize a greatest fixpoint formula with child, on variable.
        
        variable -- the variable name of the variable child depends on.
        child -- the child of the formula.
        """
        super(Nu, self).__init__(generator=generator, arguments=arguments,
                                 markers=markers,
                                 attributors=attributors,
                                 choosers=choosers)
        self.variable = variable
        self.child = child
    
    def _eval(self, fsm, context=None):
        if context is None:
            context = {}
        else:
            context = dict(context)
        
        context[self.variable] = BDD.true(fsm.bddEnc.DDmanager)
        
        old = context[self.variable]
        new = self.child.eval(fsm, context)
        while old != new:
            old = new
            context[self.variable] = old
            new = self.child.eval(fsm, context)
        
        return new
    
    def _explain(self, fsm, state, context):
        cp = self._copy()
        
        # Keep only markers needed to be kept
        for marker in self.markers:
            if not marker.keep:
                cp.markers.discard(marker)
        
        formula = self.child._substitute(self.variable, cp)
        return {Obligation(fsm, state, formula, context)}
    
    def _choices(self, fsm, state, context):
        return (self._explain(fsm, state, context), "none")
    
    def __str__(self):
        s = "nu " + str(self.variable) + "." + str(self.child)
        return super(Nu, self).__str__(s)
    
    def _no_alias(self):
        return "nu " + str(self.variable) + "." + self.child._no_alias()
    
    def __eq__(self, other):
        if type(other) is not Nu:
            return False
        else:
            return (self.variable == other.variable and
                    self.child == other.child)
    
    def __hash__(self):
        return (17 + 23 * hash("Nu") +
                23 * 23 * hash(self.variable) + 
                23 * 23 * 23 * hash(self.child))
    
    def _copy(self):
        cp = Nu(self.variable._copy(), self.child._copy(),
                generator=self.generator, arguments=self.arguments,
                markers=self.markers.copy(),
                attributors=self.attributors.copy(),
                choosers=self.choosers.copy())
        cp._substitutions = self._substitutions
        return cp
    
    def _negate(self):
        negated = Mu(self.variable._copy(),
                     self.child._substitute(self.variable,
                                            Not(self.variable))._negate(), 
                     markers=self.markers.copy(),
                     attributors=self.attributors.copy(),
                     choosers=self.choosers.copy())
        return super(Nu, self)._negate(negated)
    
    def _substitute(self, variable, other):
        if self.variable == variable:
            # New scope for variable, do not substitute further
            return self._copy()
        else:
            self_sub = Nu(self.variable._copy(),
                          self.child._substitute(variable, other),
                          markers=self.markers.copy(),
                          attributors=self.attributors.copy(),
                          choosers=self.choosers.copy())
            return super(Nu, self)._substitute(variable, other,
                                               substitution=self_sub)


# ----- ALIASES ---------------------------------------------------------------


# Pretty format
class _PrettyFormater:
    def __init__(self, format, **modifiers):
        """
        Build a pretty printer based on format and a dictionary of keywords of
        format to functions taking the initial value of the keyword and
        returning a modified version of the keyword value.
        """
        self.form = format
        self.modifiers = modifiers
    
    def format(self, *args, **kwargs):
        for k, f in self.modifiers.items():
            if k in kwargs:
                kwargs[k] = f(kwargs[k])
        return self.form.format(*args, **kwargs)

def pretty_format(**modifiers):
    """
    Return a pretty formater based on modifiers.
    
    modifiers -- a dictionary of format arguments names to functions modifying
                 these arguments.
    
    Return a new function that will reformat the arguments based on the given
    modifiers.
    """
    def pretty_formater(format):
        return _PrettyFormater(format, **modifiers)
    return pretty_formater

class _Aliaser:
    def __init__(self, generator, form, negator, translator, bounded):
        self.generator = generator
        self.form = form
        self.negator = negator
        self.translator = translator
        self.bounded = bounded
    
    def negation(self, negator):
        self.negator = negator
        return self
    
    def translation(self, translator):
        self.translator = translator
        return self
    
    def __call__(self, *args, **kwargs):
        sig = inspect.signature(self.generator)
        arg_names = [param for param in sig.parameters.keys()]
        arguments = dict(zip(arg_names, args))
        arguments.update(kwargs)
        formula = self.generator(*args, **kwargs)
        formula.generator = self
        formula.arguments = arguments
        return formula
    
    def __instancecheck__(self, instance):
        if hasattr(instance, "generator"):
            return instance.generator == self
        else:
            return False


def alias(form=None, negator=None, translator=None, bounded=None):
    """
    Return and aliased formula generator.
    
    form -- if not None, the format string for the formula generator, expressed
            in terms of arguments of the generator;
    negator -- if not None, another formula generator used to build the
               negation of the corresponding formula generated by the returned
               generator;
    translator -- if not None, a function taking a graph of attributed
                  explanation and a node and returning a new graph representing
                  the translation of the given graph;
    bounded -- if not bounded, the format string for the bounded version of
               the formula generator, expressed in terms of arguments of the
               generator, plus the special name bound, defining the bound of
               the bounded version.
    
    If form is None, a standard format string is built as the function name,
    followed by a comma-separated list of its arguments enclosed in
    parentheses; the bounded version is the same where the bound is added
    before the opening parenthesis.
    
    If form is not None but bounded is, the standard format for Mu operators
    expansion is used.
    """
    def aliaser(generator, form=form, bounded=bounded):
        if form is None:
            sig = inspect.signature(generator)
            form = (generator.__name__ + "(" +
                      ", ".join("{{{name}}}".format(name=param)
                                for param in sig.parameters.keys()) +
                      ")")
            bounded = (generator.__name__ + "^{{{bound}}}(" +
                       ", ".join("{{{name}}}".format(name=param)
                                for param in sig.parameters.keys()) +
                       ")")
        return _Aliaser(generator, form, negator, translator, bounded)
    return aliaser


# ----- MARKERS ---------------------------------------------------------------

class Marker:
    """
    A marker is used to mark a formula.
    """
    
    def __init__(self, name, keep=True):
        """
        Create a new marker with name that is kept if keep is true.
        
        name -- the string name of the marker (for printing);
        keep -- if True, kept when substituting Nu, otherwise ignored.
        """
        self.name = name
        self.keep = keep
    
    def __str__(self):
        return self.name
    
    def __repr__(self):
        return str(self)
    
    def __call__(self, formula):
        """
        Mark the formula with this marker.
        """
        formula.markers.add(self)
        return formula


POI = Marker("POI")
"""
A Point of Interest marks a formula as important, keeping the formula when
reducing an explanation that uses this formula.
"""

SPOI = Marker("SPOI", keep=False)
"""
A simple point of interest is a point of interest at some point of the
formula. Contrary to standard point of interest (POI), the SPOI is not
carried by a greatest fixpoint (Nu) when it is explained.
"""

POD = Marker("POD")
"""
A Point of Decision marks a formula to ask the explanation to stop at this
point. The formula can then be explained later.
"""

SPOD = Marker("SPOD", keep=False)
"""
A simple point of decision is a point of decision at some point of the
formula. Contrary to standard point of decision (POD), the SPOD is not
carried by a greatest fixpoint (Nu) when it is explained.
"""


# ----- ATTRIBUTORS -----------------------------------------------------------

class _Attributorer:
    
    def __init__(self, attributor):
        self.attributor = attributor
    
    @property
    def attributors(self):
        return (_ObligationAttributor(self.attributor),
                _EdgeAttributor(self.attributor))
    
    def __call__(self, formula):
        formula.attributors.append(_ObligationAttributor(self.attributor))
        formula.attributors.append(_EdgeAttributor(self.attributor))
        return formula

class _ObligationAttributorer(_Attributorer):
    
    @property
    def attributors(self):
        return (_ObligationAttributor(self.attributor),)
    
    def __call__(self, formula):
        formula.attributors.append(_ObligationAttributor(self.attributor))
        return formula

class _EdgeAttributorer(_Attributorer):
    
    @property
    def attributors(self):
        return (_EdgeAttributor(self.attributor),)
    
    def __call__(self, formula):
        formula.attributors.append(_EdgeAttributor(self.attributor))
        return formula


class _ObligationAttributor:
    def __init__(self, func):
        self.func = func
    def __call__(self, obligation):
        return self.func(obligation)

class _EdgeAttributor:
    def __init__(self, func):
        self.func = func
    def __call__(self, edge):
        return self.func(edge)


def attributor(attributor):
    """
    Return an attributor from attributor.
    
    attributor -- a function taking an annotated obligation or an annotated
                  edge (triple of annotated obligation, annotated edge,
                  annotated obligation) as argument and returning a dictionary
                  of attributes for this obligation or edge.
    """
    return _Attributorer(attributor)

def obligation_attributor(attributor):
    """
    Return an obligation attributor from attributor.
    
    attributor -- a function taking an annotated obligation as argument and
                  returning a dictionary of attributes for this obligation.
    """
    return _ObligationAttributorer(attributor)

def edge_attributor(attributor):
    """
    Return an edge attributor from attributor.
    
    attributor -- a function taking an annotated edge (triple of annotated
                  obligation, annotated edge, annotated obligation) as argument
                  and returning a dictionary of attributes for this edge.
    """
    return _EdgeAttributorer(attributor)

@edge_attributor
def _keep_transition_and_inputs(edge):
    origin = edge[0]
    if isinstance(origin.formula, Box) or isinstance(origin.formula, Diamond):
        attrs = {"transition": origin.formula.transition}
        if origin.formula.inputs:
            attrs["inputs"] = origin.formula.inputs
        return attrs
    else:
        return {}


# ----- CHOOSERS --------------------------------------------------------------

class _Chooserer:
    def __init__(self, chooser):
        self._chooser = chooser
    
    def __call__(self, formula):
        formula.choosers.append(_Chooser(self._chooser))
        return formula
    
    @property
    def chooser(self):
        return _Chooser(self._chooser)

class _Chooser:
    def __init__(self, func):
        self.func = func
    def __call__(self, obligation, choices, type_):
        return self.func(obligation, choices, type_)


def chooser(chooser):
    """
    Return a chooser from chooser.
    
    chooser -- a function taking an obligation, a set of choices and a type of
               choice ("inclusive", "exclusive" or "none") as arguments, and
               returning a subset of these choices.
    """
    return _Chooserer(chooser)