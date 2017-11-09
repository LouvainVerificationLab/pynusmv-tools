"""
Graphs inspector.

The graph inspector is a tkinter-based GUI to inspect and manipulate graphs.
"""

import tkinter as tk
import tkinter.ttk as ttk
from copy import deepcopy
from itertools import count
from collections import OrderedDict, defaultdict, Mapping, Iterable
from tkCanvasGraph import CanvasFrame, Vertex, Edge
from tkCanvasGraph.mouse import Mouse
from tkCanvasGraph.util import ObservableSet


class ObservableElement(object):
    """
    An observable element. Notifies registered observers when value changes.
    """
    def __init__(self, value=None):
        self._value = value
        self._observers = []
    
    @property
    def value(self):
        """
        The value of this element.
        """
        return self._value
    
    @value.setter
    def value(self, new_value):
        self._value = new_value
        self.notify()
    
    def notify(self):
        """
        Notify all registered observers.
        """
        for observer in self._observers:
            observer.update(self)
    
    def register(self, observer):
        """
        Register the given observer. The observer will be notified when this
        element is updated.
        
        observer -- the observer to notify; must have an update(element)
                    method.
        """
        self._observers.append(observer)

    def unregister(self, observer):
        """
        Unregister the given observer. It will not be notified any more.

        observer -- the observer to remove.
        """
        try:
            self._observers.remove(observer)
        except ValueError:
            pass


class KeysDictionary(OrderedDict):
    """
    A keys dictionary is a dictionary with key "_all_" leading to a boolean
    value, and any other key leads to keys dictionaries.
    """
    
    def __init__(self, *args, **kwargs):
        """
        Create a new keys dictionary from the given data.
        
        The given data must be compliant with the definition of keys
        dictionary.
        """
        super().__init__(*args, **kwargs)
    
    
    def merge(self, other):
        """
        Merge this keys dictionary with other
        
        second -- another keys dictionary.
        
        The result is a new keys dictionary with the keys of first and second,
        and where the values are merged, that is, if the key is _all_, the
        value is the one of second, if it exists, otherwise the value of first,
        and where the values of the other keys are recursively merged.
        """
        first = deepcopy(self)
        for key, value in other.items():
            if key in first and isinstance(value, KeysDictionary):
                first[key] = first[key].merge(value)
            else: # key is not in first or key is _all_
                first[key] = value
        return first

    def some(self, value):
        """
        Return whether somes keys of this keys dictionary have value or not
        (recursively).
        
        value -- a boolean.
        """
        for k, v in self.items():
            if v == value:
                return True
            if isinstance(v, KeysDictionary) and v.some(value):
                return True
        return False

    def set_all(self, value):
        """
        Recursively set all values of this keys dictionary to value.
        
        value -- a boolean.
        """
        self["_all_"] = value
        for k, v in self.items():
            if isinstance(v, KeysDictionary):
                v.set_all(value)

    def hide_empty(self):
        """
        For all keys where all subkeys are not visible, set the keys as
        non-visible, recursively.
        """
        all_false = True
        for key, value in self.items():
            if key != "_all_":
                value.hide_empty()
                if value.some(True):
                    all_false = False
        if all_false and len(self) > 1:
            self["_all_"] = False

    def show_nonempty(self):
        """
        For all keys where some subkeys are visible, set the keys as visible,
        recursively.
        """
        some_true = False
        for key, value in self.items():
            if key != "_all_":
                value.show_nonempty()
                if value.some(True):
                    some_true = True
        if some_true:
            self["_all_"] = True

    def harmonize(self):
        """
        For all keys where all subkeys are not visible, set the keys as
        non-visible, recursively.
        For all keys where some subkeys are visible, set the keys as visible,
        recursively.
        """
        self.hide_empty()
        self.show_nonempty()


class GraphVertex(Vertex):
    """
    A vertex representing a graph node.
    """
    def __init__(self, inspector, node):
        super().__init__(inspector.canvas)
        self.node = node
        
        # The values to display as label
        # if node contains a _label_ key, use it as the values:
        #   if _label_ is callable, call it and analyse the result further
        #   if _label_ (or the result of the call) is a string,
        #   use it directly as the label
        #   otherwise, use the value of _label_ (or the result of the call)
        #   as it is
        # otherwise, the node itself (a dictionary) is used as the values

        if callable(node._label_):
            values = node._label_(inspector)
        else:
            values = node._label_
        if values is None:
            values = node
        self._label_values = values
        
        # The view of the vertex
        # if node contains a _view_ key, use it as the values:
        #   if _view_ is callable, call it and analyse the result further
        #   then use the value of _view_ (or the result of the call) as it is
        # otherwise, the node itself (a dictionary) is used as the values
        if callable(node._view_):
            view = node._view_(inspector)
        else:
            view = node._view_
        if view is None:
            view = node
        self._view = view
        
        # The menu of the vertex
        # if node contains a _menu_ key, use it as the menu:
        #   if _menu_ is callable, call it and analyse the result further
        #   then use the value of _menu_ (or the result of the call) as it is
        # otherwise, no menu is considered
        if callable(node._menu_):
            menu = node._menu_(inspector)
        else:
            menu = node._menu_
        self._menu = menu
    
    @property
    def data(self):
        return self.node
    
    @property
    def label_values(self):
        return self._label_values
    
    @property
    def view(self):
        return self._view
    
    @property
    def menu(self):
        return self._menu


class GraphEdge(Edge):
    """
    An edge representing a graph edge.
    """
    def __init__(self, inspector, origin, end, edge):
        super().__init__(inspector.canvas, origin, end)
        self.edge = edge
        
        # The values to display as label
        # if edge contains a _label_ key, use it as the values:
        #   if _label_ is callable, call it and analyse the result further
        #   if _label_ (or the result of the call) is a string,
        #   use it directly as the label
        #   otherwise, use the value of _label_ (or the result of the call)
        #   as it is
        # otherwise, the edge itself (a dictionary) is used as the values
        if callable(edge._label_):
            values = edge._label_(inspector)
        else:
            values = edge._label_
        if values is None:
            values = edge
        self._label_values = values
        
        # The view of the edge
        # if edge contains a _view_ key, use it as the values:
        #   if _view_ is callable, call it and analyse the result further
        #   then use the value of _view_ (or the result of the call) as it is
        # otherwise, the edge itself (a dictionary) is used as the values
        if callable(edge._view_):
            view = edge._view_(inspector)
        else:
            view = edge._view_
        if view is None:
            view = edge
        self._view = view
        
        # The menu of the edge
        # if edge contains a _menu_ key, use it as the menu:
        #   if _menu_ is callable, call it and analyse the result further
        #   then use the value of _menu_ (or the result of the call) as it is
        # otherwise, no menu is considered
        if callable(edge._menu_):
            menu = edge._menu_(inspector)
        else:
            menu = edge._menu_
        self._menu = menu
    
    @property
    def data(self):
        return self.edge
    
    @property
    def label_values(self):
        return self._label_values
    
    @property
    def view(self):
        return self._view
    
    @property
    def menu(self):
        return self._menu


class GraphFrame(CanvasFrame):
    """
    A frame displaying a graph.
    """
    pass


def _get_path(elements):
    """
    Return the path represented by elements, or None if elements does
    not define a path.
    
    elements -- a set of elements.
    
    The returned path is a list where vertices alternate with edges.
    The elements might define a loop; in this case, the first vertex is chosen
    arbitrarily.
    The elements might define a lasso; in this case, the first unrolling of the
    loop is exposed.
    """
    edges = {e for e in elements if isinstance(e, GraphEdge)}
    vertices = {e for e in elements if isinstance(e, GraphVertex)}
    graph = {v: {e for e in edges if e.origin == v}
             for v in vertices}
    
    # Get source
    sources = {v for v in graph
               if len({e for e in edges if e.end == v}) <= 0}
    if len(sources) > 1:
        # More than one source, it does not define a single path
        return None
    elif not sources:
        # No source, pick any vertex
        source = next(iter(vertices))
    else:
        # One source
        source = next(iter(sources))
    
    path = [source]
    while True:
        outgoings = graph[path[-1]]
        if len(outgoings) > 1:
            # More than one outgoing edge, this is not a single path
            return None
        elif not outgoings:
            # No more nodes, end of path
            break
        
        outgoing = next(iter(outgoings))
        
        if outgoing.end in path:
            # we reach a loop
            path.append(outgoing)
            path.append(outgoing.end)
            break
        
        else:
            path.append(outgoing)
            path.append(outgoing.end)
    
    return path


class PathInspectorFrame(tk.Frame):
    """
    A frame to inspect a path in a graph.
    """
    def __init__(self, inspected, parent, **config):
        """
        Create a new inspector for the given observable set of elements.
        
        inspected -- an observable set of elements.
        """
        super(PathInspectorFrame, self).__init__(parent, **config)
        self.content = tk.Frame(master=self)
        self.content.pack(fill=tk.BOTH, expand=True)
        # Register to the explanations set
        self.inspected = inspected
        inspected.register(self)
        
        self.update(inspected)
    
    def _remove_content(self):
            """
            Remove the content of this frame.
            """
            self.content.destroy()
            self.content = tk.Frame(self)
            self.content.pack(fill=tk.BOTH, expand=True)

    def update(self, inspected):
        """
        Update this frame to show inspected path.
        """
        self._remove_content()
        
        if len(inspected) <= 0:
            label = tk.Label(self.content, text="No inspected path.")
            label.pack()
        else:
            path = _get_path(inspected)
            if path is None:
                label = tk.Label(self.content,
                                 text=
                                 "Highlighted elements do not define a path.")
                label.pack()
            else:
                # Treeview for paths
                
                vertices = [path[0]] + path[2::2]
                edges = path[1::2]
                
                # Create the treeview
                self.content.grid_rowconfigure(0, weight=1)
                self.content.grid_columnconfigure(0, weight=1)
                treeview = ttk.Treeview(self.content,
                                        columns=["c" + str(i) for i in
                                                 range(len(vertices))])
                # Set columns widths
                treeview.column("#0", width=50)
                for col in range(len(vertices)):
                    treeview.column("c" + str(col), width=50)
                
                treeview.heading("#0", text="Key")
                for col in range(len(vertices)):
                    treeview.heading("c" + str(col),
                                     text="Value " + str(col + 1))
                
                # Add scrollbars
                ysb = tk.Scrollbar(self.content, orient=tk.VERTICAL,
                                   command=treeview.yview)
                xsb = tk.Scrollbar(self.content, orient=tk.HORIZONTAL,
                                    command=treeview.xview)
                treeview.configure(yscrollcommand=ysb.set,
                                   xscrollcommand=xsb.set)
                
                treeview.grid(row=0, column=0, sticky=tk.W+tk.E+tk.N+tk.S)
                ysb.grid(row=0, column=1, sticky=tk.NS)
                xsb.grid(row=1, column=0, sticky=tk.EW)
                
                # Get views and keys
                vertices_views = [vertex.view for vertex in vertices]
                edges_views = [edge.view for edge in edges]
                vertices_keys = get_all_keys(vertices_views)
                edges_keys = get_all_keys(edges_views)
                
                # Gather data
                # Get a dictionary with one list of lists in _all_
                # and other keys contain similar dictionaries
                # the ith list of _all_ contains the list of values to display
                # for the ith element of the path
                # the other keys lead to similar dictionaries containing
                # the values in the different elements of the path, under
                # the corresponding key
                def gather_data(view, view_id, nbviews, gatherer=None):
                    if gatherer is None:
                        gatherer = OrderedDict()
                    
                    if isinstance(view, Mapping):
                        for key, value in view.items():
                            if not str(key).startswith("_"):
                                if key not in gatherer:
                                    gatherer[key] = OrderedDict()
                                gather_data(value,
                                            view_id,
                                            nbviews,
                                            gatherer[key])
                    
                    elif (isinstance(view, Iterable) and
                          not isinstance(view, str)):
                        for element in view:
                            gather_data(element, view_id, nbviews, gatherer)
                    
                    else:
                        if "_all_" not in gatherer:
                            gatherer["_all_"] = [[] for _ in range(nbviews)]
                        gatherer["_all_"][view_id].append(view)
                    
                    if "_all_" in gatherer:
                        gatherer.move_to_end("_all_", last=False)
                    
                    return gatherer
                
                vertices_data = None
                for i, view in enumerate(vertices_views):
                    vertices_data = gather_data(view,
                                                i,
                                                len(vertices_views),
                                                gatherer=vertices_data)
                
                edges_data = None
                edges_views = [{}] + edges_views
                for i, view in enumerate(edges_views):
                    edges_data = gather_data(view,
                                             i,
                                             len(edges_views),
                                             gatherer=edges_data)
                
                # Add data to treeview
                curid = count(1)
                def add_data(treeview, data, parentid):
                    # data is a list of lists
                    while data != [[]] * len(data):
                        values = []
                        for view in data:
                            if len(view):
                                values.append(view.pop(0))
                            else:
                                values.append("")
                        iid = parentid + str(next(curid))
                        treeview.insert(parentid,
                                        "end",
                                        iid=iid,
                                        value=values)
                
                def add(treeview, data, parentid):
                    # data is a dictionary
                    if "_all_" in data:
                        add_data(treeview, data["_all_"], parentid)
                    for key, values in data.items():
                        if not str(key).startswith("_"):
                            iid = parentid + key
                            
                            if (len(values) <= 1 and
                                "_all_" in values and
                                all(len(view) <= 1
                                    for view in values["_all_"])):
                                vv = [(str(view.pop(0))
                                       if len(view)
                                       else "")
                                      for view in values["_all_"]]
                                treeview.insert(parentid,
                                                "end",
                                                iid=iid,
                                                text=str(key),
                                                open=True,
                                                values=vv)
                            
                            else:
                                treeview.insert(parentid,
                                                "end",
                                                iid=iid,
                                                text=str(key),
                                                open=True)
                                add(treeview, values, iid)
                
                add(treeview, edges_data, "")
                treeview.insert("", "end")
                add(treeview, vertices_data, "")


class InspectorModifyingMouse(Mouse):
    """
    A mouse that adds and removes inspected elements
    """
    
    def __init__(self, inspected, edges):
        super(InspectorModifyingMouse, self).__init__()
        self.inspected = inspected
        self.edges = edges
    
    def pressed(self, event):
        """
        React to mouse button pressed.
        """
        element = event.element
        if element is not None:
            if element not in self.inspected:
                if isinstance(element, GraphEdge):
                    self.inspected.add(element.origin)
                    self.inspected.add(element.end)
                self.inspected.add(element)
            else:
                if isinstance(element, GraphVertex):
                    for edge in self.edges:
                        if (edge.origin == element or
                            edge.end == element):
                            self.inspected.discard(edge)
                self.inspected.discard(element)
            
            event.canvas.refresh()
            return False
        return True

class PathInspectingMouse(Mouse):
    """
    A mouse that inspect one path.
    """
    
    def __init__(self, inspected, vertices, edges):
        """
        inspected -- the observable set of inspected elements;
        vertices -- the set of vertices of the canvas;
        edges the set of edges of the canvas.
        """
        super(PathInspectingMouse, self).__init__()
        self.inspected = inspected
        self.vertices = vertices
        self.edges = edges
        
        self.arrow = None
        self.start_arrow = None
        
        self.is_pressed = False
        self.start = None
    
    def pressed(self, event):
        """Mouse button pressed."""
        self.start = event.element
        
        if event.element is not None:
            self.start_arrow = event.position
        return True
    
    def moved(self, event):
        """Mouse moved."""
        def delta(a, b):
            if a > b:
                return a - b
            else:
                return b - a
        
        if self.start_arrow is not None:
            delta_x = delta(self.start_arrow[0], event.position[0])
            delta_y = delta(self.start_arrow[1], event.position[1])
            if delta_x > 2 or delta_y > 2:
                if self.arrow is None:
                    self.arrow = event.canvas.create_line(self.start_arrow +
                                                          self.start_arrow,
                                                          fill="gray",
                                                          arrow="last",
                                                          width=3)
                end_position = ((event.position[0] + 2)
                                if event.position[0] < self.start_arrow[0]
                                else (event.position[0] - 2),
                                (event.position[1] + 2)
                                if event.position[1] < self.start_arrow[1]
                                else (event.position[1] - 2))
            
                coords = self.start_arrow + end_position
                event.canvas.coords(self.arrow, *coords)
        return True
    
    def released(self, event):
        """Mouse button released."""
        self.inspected.clear()
        element = event.element
        
        # If on start, select start (and ends if an edge)
        if element == self.start:
            if isinstance(element, Vertex):
                self.inspected.add(element)
            elif isinstance(element, Edge):
                self.inspected.add(element.origin)
                self.inspected.add(element.end)
                self.inspected.add(element)
        
        # If on another than start, and both are vertices, select path
        elif (isinstance(self.start, Vertex) and
              isinstance(element, Vertex)):
              # Get shortest path
              path = self.shortest_path(self.start, element)
              # Highlight the shortest path
              if path is not None:
                  self.inspected.clear()
                  self.inspected.update(path)
        
        # Else, inspect nothing
        
        # Remove arrow
        if self.arrow is not None:
            event.canvas.delete(self.arrow)
            self.arrow = None
        self.start_arrow = None
        
        event.canvas.refresh()
        
        self.start = None
        return True
    
    def shortest_path(self, start, end):
        """
        Return the shortest path between start and end.
        
        Return None if no such path exists.
        """
        graph = {v: {e for e in self.edges if e.origin == v}
                 for v in self.vertices}
        
        pred = {start: None}
        to_expand = [start]
        
        # BFS
        while len(to_expand) > 0 and end not in pred:
            current = to_expand[0]
            to_expand = to_expand[1:]
            
            for edge in graph[current]:
                if edge.end not in pred:
                    to_expand.append(edge.end)
                    pred[edge.end] = current
        
        if end not in pred:
            return None
        
        # Build path
        path = [end]
        while path[-1] != start:
            o, e = pred[path[-1]], path[-1]
            edge = next(iter({ed for ed in graph[o] if ed.end == e}))
            path.append(edge)
            path.append(o)
        path.reverse()
        
        return path


class ElementInspectorFrame(tk.Frame):
    """
    A frame to inspect a particular element.
    """
    
    def __init__(self, inspected, parent, **config):
        """
        Create a new inspector for the given observable element.
        
        inspected -- an observable element.
        """
        # Create the frame
        super(ElementInspectorFrame, self).__init__(parent, **config)
        self.content = tk.Frame(master=self)
        self.content.pack(fill=tk.BOTH, expand=True)
        # Register to the explanations set
        self.inspected = inspected
        inspected.register(self)
        
        self.update(inspected)
    
    def _remove_content(self):
        """
        Remove the content of this frame.
        """
        self.content.destroy()
        self.content = tk.Frame(self)
        self.content.pack(fill=tk.BOTH, expand=True)
    
    def update(self, inspected):
        """
        Update this frame to show inspected element.
        """
        self._remove_content()
        
        def has_keys(view):
            if isinstance(view, Mapping):
                return True
            elif isinstance(view, Iterable) and not isinstance(view, str):
                for element in view:
                    if has_keys(element):
                        return True
                return False
            else:
                return False
        
        if not inspected.value:
            label = tk.Label(self.content, text="No inspected element.")
            label.pack()
        else:
            element = inspected.value
            view = element.view
            
            self.content.grid_rowconfigure(0, weight=1)
            self.content.grid_columnconfigure(0, weight=1)
            
            if has_keys(view):
                curid = count(1)
                def add(treeview, element, parentid):
                    if isinstance(element, Mapping):
                        for key, value in element.items():
                            if not str(key).startswith("_"):
                                iid = (parentid +
                                       "." +
                                       str(key) +
                                       str(next(curid)))
                                if (isinstance(value, Mapping) or
                                    (isinstance(value, Iterable) and
                                     not isinstance(value, str))):
                                    treeview.insert(parentid,
                                                    "end",
                                                    iid=iid,
                                                    text=str(key),
                                                    open=True)
                                    add(treeview, value, iid)
                                else:
                                    treeview.insert(parentid,
                                                    "end",
                                                    iid=iid,
                                                    text=str(key),
                                                    value=(str(value),))
                    elif (isinstance(element, Iterable) and
                          not isinstance(element, str)):
                        for value in element:
                            add(treeview, value, parentid)
                    else:
                        iid = parentid + "." + str(next(curid))
                        treeview.insert(parentid,
                                        "end",
                                        iid=iid,
                                        value=(str(element),))
                
                treeview = ttk.Treeview(self.content, columns=["value"])
                
                treeview.heading("#0", text="Key")
                treeview.heading("value", text="Value")
                
                treeview.column("#0", width=100)
                treeview.column("value", width=100)
                
                add(treeview, view, "")
            
            else: # not has_keys(view)
                def add(treeview, element):
                    if (isinstance(element, Iterable) and
                        not isinstance(element, str)):
                        for value in element:
                            add(treeview, value)
                    else:
                        treeview.insert("", "end",
                                        iid=str(element),
                                        text=str(element),
                                        values=())
                
                treeview = ttk.Treeview(self.content, columns=[])
                treeview.column("#0", width=100)
                
                add(treeview, view)
            
            ysb = tk.Scrollbar(self.content, orient=tk.VERTICAL,
                               command=treeview.yview)
            xsb = tk.Scrollbar(self.content, orient=tk.HORIZONTAL,
                                command=treeview.xview)
            treeview.configure(yscrollcommand=ysb.set,
                               xscrollcommand=xsb.set)
            
            treeview.grid(row=0, column=0, sticky=tk.W+tk.E+tk.N+tk.S)
            ysb.grid(row=0, column=1, sticky=tk.NS)
            xsb.grid(row=1, column=0, sticky=tk.EW)


class ElementInspectorMouse(Mouse):
        """
        A mouse that inspects one element.
        """
        
        def __init__(self, inspected):
            super(ElementInspectorMouse, self).__init__()
            self.inspected = inspected
        
        def pressed(self, event):
            """
            React to mouse button pressed.
            """
            self.inspected.value = event.element
            event.canvas.refresh()
            return False

class KeysChooserMouse(Mouse):
        """
        A mouse that choose the keys to display.
        """
        
        def __init__(self, inspector):
            super(KeysChooserMouse, self).__init__()
            self.inspector = inspector
        
        def pressed(self, event):
            """
            React to mouse button pressed.
            """
            
            def menu_for_keys(keys, parent, top_keys):
                """
                Return the menu for the given keys dictionary.
                
                keys -- a keys dictionary.
                parent -- the parent of the created menu.
                """
                # List the keys, except _all_
                # If the corresponding value is only {"_all_": val},
                # make it a checkable menu item
                # otherwise make it a cascading menu with the menu for the
                # keys
                menu = tk.Menu(parent)
                for key, value in keys.items():
                    if key != "_all_":
                        if len(value) == 1: # Only "_all_"
                            bvar = tk.BooleanVar()
                            bvar.set(value["_all_"])
                            def callback(*args,
                                         bvar=bvar,
                                         value=value):
                                value["_all_"] = bool(bvar.get())
                                top_keys.harmonize()
                                event.canvas.refresh()
                            bvar.trace("w", callback)
                            menu.add_checkbutton(label=key,
                                                 onvalue=True,
                                                 offvalue=False,
                                                 variable=bvar)
                        
                        else: # Some sub keys
                            submenu = menu_for_keys(value, menu, top_keys)
                            menu.add_cascade(menu=submenu, label=key)
                
                # Special treatment if top-level is only _all_
                if len(keys) == 1:
                    def callback(*args):
                        keys["_all_"] = not keys["_all_"]
                        top_keys.harmonize()
                        event.canvas.refresh()
                    label = "Hide" if keys["_all_"] else "Show"
                    menu.add_command(label=label, command=callback)
                
                menu.add_separator()
                
                # If there is more than one key
                # If some are displayed, add Hide all
                # If some are hidden, add Show all
                if len(keys) > 2:
                    def hide_all():
                        keys.set_all(False)
                        event.canvas.refresh()
                    def show_all():
                        keys.set_all(True)
                        event.canvas.refresh()
                    if keys.some(True):
                        menu.add_command(label="Hide all",
                                         command=hide_all)
                    if keys.some(False):
                        menu.add_command(label="Show all",
                                         command=show_all)
                
                return menu
            
            if event.element is None:
                menu = tk.Menu(event.canvas)
                display_menu = tk.Menu(menu)
                
                nodes_menu = menu_for_keys(self.inspector.nodes_keys,
                                           display_menu,
                                           self.inspector.nodes_keys)
                
                edges_menu = menu_for_keys(self.inspector.edges_keys,
                                           display_menu,
                                           self.inspector.edges_keys)
                
                display_menu.add_cascade(menu=nodes_menu, label="Vertices")
                display_menu.add_cascade(menu=edges_menu, label="Edges")
                menu.add_cascade(menu=display_menu, label="Display")
                
                menu.post(*event.absolute)
                return False
            
            else:
                # No handling for single element menu
                return True


class CustomMenuMouse(Mouse):
    """
    Display the menu on vertices and edges if present.
    """
    
    def pressed(self, event):
        """
        React to mouse button pressed.
        """
        if event.element is not None:
            menu = event.element.menu
            if menu is not None:
                menu.post(*event.absolute)
                return False
            else:
                return True
        else:
            return True


def label(element, displayed_keys):
    """
    Return the label of the element.
    
    element -- the element to get the label from.
    displayed_keys -- the keys to display.
    """
    
    def indent(text, size=4, chr=" "):
        """
        Indent the given text with size occurrences of chr.
        """
        return "\n".join(size * chr + line for line in text.split("\n"))
    
    values = element
    if isinstance(values, str):
        if displayed_keys["_all_"]:
            return values
        else:
            return ""
    
    # Build the string (values is either an iterable or a mapping)
    #
    # mappings are displayed as:
    #   key = value, where value is recursively built with the same process
    # only keys that do not start with _ are used
    #
    # iterables (other than strings) are displayed one value per line
    # (where the values are recursively built with the same process)
    #
    # if a value is more than one line long (contains a newline),
    # it is indented with 4 spaces and printed on a new line
    
    # To define what should be displayed,
    # displayed_keys is a dictionary
    #   with key _all_ telling whether the whole element should be displayed
    #   or not
    #   and with the keys of the dictionary telling whether they should be
    #   displayed invididually.
    
    def build_iterable(values, displayed_keys=None):
        if displayed_keys is not None and displayed_keys["_all_"]:
            built = []
            for element in values:
                if isinstance(element, Mapping):
                    built_element = build_mapping(element, displayed_keys)
                elif (isinstance(element, Iterable) and
                      not isinstance(element, str)):
                    built_element = build_iterable(element, displayed_keys)
                else:
                    built_element = str(element)
                
                built.append(built_element)
            
            return "\n".join(built)
        else:
            return ""
        
    def build_mapping(values, displayed_keys=None):
        if displayed_keys is not None and displayed_keys["_all_"]:
            built = []
            for key, element in values.items():
                if (not str(key).startswith("_") and
                    displayed_keys[key]["_all_"]):
                    
                    if isinstance(element, Mapping):
                        built_element = build_mapping(element,
                                                      displayed_keys=
                                                      displayed_keys[key])
                    elif (isinstance(element, Iterable) and
                          not isinstance(element, str)):
                        built_element = build_iterable(element,
                                                       displayed_keys=
                                                       displayed_keys[key])
                    else:
                        built_element = str(element)
                    
                    if built_element.find("\n") >= 0:
                        built.append(str(key) +
                                     " =\n" +
                                     indent(built_element))
                    else:
                        built.append(str(key) +
                                     " = " +
                                     built_element)
            
            return "\n".join(built)
        else:
            return ""
    
    if isinstance(values, Mapping):
        return build_mapping(values, displayed_keys=displayed_keys)
    else: # isinstance(values, Iterable)
        return build_iterable(values, displayed_keys=displayed_keys)


def element_keys(element, follow=None):
    """
    Return the keys dictionary of element.
    
    element -- any data structure.
    follow -- a keys dictionary from which the values will be extracted
              for the keys appearing in element.
    
    If element is a Mapping, returns {"_all_": True} augmented with the
    keys dictionary for the other keys, otherwise return {"_all_": True}.
    If follow is not None, the boolean values are retrieved from follow
    for the keys in common.
    
    """
    if follow is None:
        follow = KeysDictionary()
    
    if "_all_" in follow:
        keys = KeysDictionary(_all_=follow["_all_"])
    else:
        keys = KeysDictionary(_all_=True)
    
    if isinstance(element, Mapping):
        for key, value in element.items():
            if not str(key).startswith("_"):
                if key in follow:
                    keys[key] = element_keys(value, follow=follow[key])
                else:
                    keys[key] = element_keys(value)
    
    elif isinstance(element, Iterable) and not isinstance(element, str):
        for value in element:
            keys = keys.merge(element_keys(value, follow=follow))
    
    return keys


def get_all_keys(elements, follow=None):
    """
    Return the merged keys dictionary of all elements, in the given other.
    
    elements -- an iterable of data structures.
    follow -- a keys dictionary from which the values will be extracted
              for the keys appearing in element.
    
    Note: the result contains at least {"_all_": True}, even if the iterable is
    empty.
    If follow is not None, the boolean values are retrieved from follow
    for the keys in common.
    """
    
    if follow is None:
        follow = KeysDictionary()
    
    if "_all_" in follow:
        keys = KeysDictionary(_all_=follow["_all_"])
    else:
        keys = KeysDictionary(_all_=True)
    
    for element in elements:
        keys = keys.merge(element_keys(element, follow=follow))
    
    return keys


class InspectorFrame(tk.Frame):
    """
    An inspector frame. Inspect a given graph.
    """
    def __init__(self, graph, parent, data=None, **config):
        """
        Create a new inspector for graph.
        The new inspector frame gets the given parent as parent.
        
        graph -- a relational graph.
        parent -- a tkinter widget.
        config -- a possible frame configuration.
        data -- any additional data to store in the inspector.
        """
        super().__init__(parent, **config)
        
        self.data = data
        
        self._graph = graph
        
        self._inspected_element = ObservableElement()
        self._inspected_path = ObservableSet()
        
        # Populate the window:
        #   One paned window with:
        #       a graph frame on the left
        #       a ttk notebook on the right with:
        #           an Inspect tab
        vertical_split = ttk.PanedWindow(parent, orient=tk.VERTICAL)
        vertical_split.pack(fill=tk.BOTH, expand=True)

        horizontal_split = ttk.PanedWindow(vertical_split,
                                           orient=tk.HORIZONTAL)
        horizontal_split.pack(fill=tk.BOTH, expand=True)
        vertical_split.add(horizontal_split, weight=1)

        # Graph frame
        graph_frame = GraphFrame(horizontal_split)
        self._graph_frame = graph_frame
        graph_frame.pack(fill=tk.BOTH, expand=True)
        horizontal_split.add(graph_frame, weight=1)

        # Element inspector frame
        element_inspector_frame = tk.Frame(horizontal_split)
        element_inspector_title = tk.Label(element_inspector_frame,
                                           text="Element inspector",
                                           font="-weight bold")
        element_inspector_title.pack(fill=tk.NONE, expand=False, anchor=tk.NW)

        element_inspector = ElementInspectorFrame(self._inspected_element,
                                                  element_inspector_frame)
        element_inspector.pack(fill=tk.BOTH, expand=True)
        element_inspector_frame.pack(fill=tk.BOTH, expand=True)
        horizontal_split.add(element_inspector_frame)

        # Path inspector frame
        path_inspector_frame = tk.Frame(vertical_split)
        path_inspector_title = tk.Label(path_inspector_frame,
                                        text="Path inspector",
                                        font="-weight bold")
        path_inspector_title.pack(fill=tk.NONE, expand=False, anchor=tk.NW)
        path_inspector = PathInspectorFrame(self._inspected_path,
                                            path_inspector_frame)
        path_inspector.pack(fill=tk.BOTH, expand=True)
        path_inspector_frame.pack(fill=tk.BOTH, expand=True)
        vertical_split.add(path_inspector_frame)


        # Populate the canvas
        self._elements = {}
        for node in graph.nodes:
            self._elements[node] = GraphVertex(self, node)
            graph_frame.canvas.add_vertex(self._elements[node])

        for origin, edge, end in graph.edges:
            self._elements[(origin, edge, end)] = GraphEdge(self,
                                                      self._elements[origin],
                                                      self._elements[end],
                                                      edge)
            graph_frame.canvas.add_edge(self._elements[(origin, edge, end)])


        self.nodes_keys = get_all_keys(element.label_values
                                       for element in self._elements.values()
                                       if isinstance(element, GraphVertex))
        self.edges_keys = get_all_keys(element.label_values
                                       for element in self._elements.values()
                                       if isinstance(element, GraphEdge))

        # Mouses
        element_inspector_mouse = ElementInspectorMouse(self.
                                                        _inspected_element)
        graph_frame.canvas.register_mouse(element_inspector_mouse,
                                          button="1",
                                          modifiers="Alt")

        imm = InspectorModifyingMouse(self._inspected_path,
                                      graph_frame.canvas.edges)
        graph_frame.canvas.register_mouse(imm, button="1",
                                          modifiers="Control-Shift")

        pm = PathInspectingMouse(self._inspected_path,
                                 graph_frame.canvas.vertices,
                                 graph_frame.canvas.edges)
        graph_frame.canvas.register_mouse(pm, button="1", modifiers="Control")

        kcm = KeysChooserMouse(self)
        graph_frame.canvas.register_mouse(kcm, button="2")

        cmm = CustomMenuMouse()
        graph_frame.canvas.register_mouse(cmm, button="2")


        # Transformers
        def label_transformer(element, style):
            if isinstance(element, GraphVertex):
                keys = self.nodes_keys
            else: # GraphEdge
                keys = self.edges_keys

            keys = element_keys(element.label_values, follow=keys)
            keys.harmonize()

            element_label = label(element.label_values, keys)
            style["label"] = element_label
        graph_frame.canvas.register_transformer(label_transformer)

        def element_inspector_transformer(element, style):
            if element == self._inspected_element.value:
                style["shape_style"]["dash"] = 3
            else:
                style["shape_style"]["dash"] = ()
        graph_frame.canvas.register_transformer(element_inspector_transformer)

        def path_inspector_transformer(element, style):
            if (not self._inspected_path) or (element in self._inspected_path):
                style["shape_style"]["outline"] = "black"
                if isinstance(element, GraphEdge):
                    style["arrow_style"]["fill"] = "black"
            else:
                style["shape_style"]["outline"] = "gray"
                if isinstance(element, GraphEdge):
                    style["arrow_style"]["fill"] = "gray"
        graph_frame.canvas.register_transformer(path_inspector_transformer)
    
    @property
    def canvas(self):
        """
        The canvas displaying the graph.
        """
        return self._graph_frame.canvas
    
    @property
    def graph(self):
        """
        The displayed graph.
        """
        return self._graph
    
    @graph.setter
    def graph(self, new_graph):
        # Update the graph
        # Must update:
        #   - the graph itself
        #   - the canvas
        #   - the inspected element
        #   - the inspected path
        #   - the elements dictionary
        #   - the nodes keys
        #   - the edges keys
        
        def remove_element(element):
            """
            Remove the given element from all data structures
            (except the graph).
            
            element -- a displayed graph element.
            """
            self._graph_frame.canvas.delete_element(self._elements[element])
            if self._inspected_element.value == self._elements[element]:
                self._inspected_element.value = None
            self._inspected_path.discard(self._elements[element])
            del self._elements[element]
        
        def add_node(node):
            """
            Add the given node to all necessary data structures (except the
            graph).
            
            node -- a new node.
            """
            # Add the node in canvas and elements dictionary
            self._elements[node] = GraphVertex(self, node)
            self._graph_frame.canvas.add_vertex(self._elements[node])
        
        def add_edge(edge):
            """
            Add the given edge to all necessary data structures (except the
            graph).
            
            edge -- a new edge.
            """
            # Add the edge in canvas and elements dictionary
            origin, edge, end = edge
            self._elements[(origin, edge, end)] = GraphEdge(
                                                      self,
                                                      self._elements[origin],
                                                      self._elements[end],
                                                      edge)
            self._graph_frame.canvas.add_edge(self._elements[(origin,
                                                              edge,
                                                              end)])
        
        
        # Remove deleted edges
        for edge in set(self._graph.edges) - set(new_graph.edges):
            remove_element(edge)
        
        # Remove deleted nodes
        for node in set(self._graph.nodes) - set(new_graph.nodes):
            remove_element(node)
        
        # Add new nodes
        for node in set(new_graph.nodes) - set(self._graph.nodes):
            add_node(node)
        
        # Add new edges
        for edge in set(new_graph.edges) - set(self._graph.edges):
            add_edge(edge)
        
        # Update nodes keys and edges keys
        self.nodes_keys = get_all_keys((element.label_values
                                        for element in self._elements.values()
                                        if isinstance(element, GraphVertex)),
                                       follow=self.nodes_keys)
        self.nodes_keys.harmonize()
        self.edges_keys = get_all_keys((element.label_values
                                        for element in self._elements.values()
                                        if isinstance(element, GraphEdge)),
                                       follow=self.edges_keys)
        self.edges_keys.harmonize()
        
        # Update the graph
        self._graph = new_graph
    
    @property
    def inspected_element(self):
        """
        The currently inspected element (None if no element is inspected).
        The inspected element is the actual element of the inspected graph.
        """
        return self._inspected_element.value.data
    
    @inspected_element.setter
    def inspected_element(self, new_value):
        # new_value is an element of the graph
        self._inspected_element.value = self._elements[new_value]
    
    @property
    def inspected_path(self):
        """
        The currently inspected path (None if no path is inspected or the set
        of inspected elements does not define a path).
        This path is represented by a tuple of vertices and edges of the
        inspected graph, starting and ending with a vertex and alternating
        between vertices and edges.
        """
        path = _get_path(self._inspected_path)
        if path is None:
            return path
        else:
            return tuple(element.data for element in path)
    
    @inspected_path.setter
    def inspected_path(self, new_path):
        # new_path is an iterable of elements of the inspected graph
        self._inspected_path.clear()
        self._inspected_path |= {self._elements[element]
                                 for element in new_path}


def inspect(graph, parent=None, data=None):
    """
    Open an inspector for the given graph. If parent is not None,
    the new inspector window gets the given parent as parent.
    
    graph -- the graph to inspect;
    parent -- if not None, a tkinter widget.
    data -- any additional data to store in the inspector.
    """
    # Create window
    if parent is None:
        root = tk.Tk()
        mainloop = True
    else:
        root = tk.Toplevel(parent)
        mainloop = False
    
    inspector = InspectorFrame(graph, parent=root, data=data)
    
    if mainloop:
        root.mainloop()