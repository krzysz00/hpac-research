# Stubs for matchpy.matching.bipartite (Python 3.6)
#
# NOTE: This dynamically typed stub was automatically generated by stubgen.

from graphviz import Digraph, Graph
from typing import TYPE_CHECKING
if TYPE_CHECKING:
    Hashable = object
else:
    from typing import Hashable
from typing import Dict, Generic, Iterator, List, MutableMapping, Set, Tuple, TypeVar, Union

TLeft = TypeVar('TLeft', bound=Hashable)
TRight = TypeVar('TRight', bound=Hashable)
TEdgeValue = TypeVar('TEdgeValue')
Node = Tuple[int, Union[TLeft, TRight]]
NodeList = List[Node]
NodeSet = Set[Node]
Edge = Tuple[TLeft, TRight]

class BipartiteGraph(Generic[TLeft, TRight, TEdgeValue], MutableMapping[Tuple[TLeft, TRight], TEdgeValue]):
    def __init__(self, *args, **kwargs) -> None: ...
    def __setitem__(self, key: Edge, value: TEdgeValue) -> None: ...
    def __getitem__(self, key: Edge) -> TEdgeValue: ...
    def __delitem__(self, key: Edge) -> None: ...
    def edges_with_labels(self): ...
    def edges(self): ...
    def clear(self): ...
    def __copy__(self): ...
    def __iter__(self): ...
    def __len__(self): ...
    def __eq__(self, other): ...
    def as_graph(self) -> Graph: ...
    def find_matching(self) -> Dict[TLeft, TRight]: ...
    def without_nodes(self, edge: Edge) -> BipartiteGraph[TLeft, TRight, TEdgeValue]: ...
    def without_edge(self, edge: Edge) -> BipartiteGraph[TLeft, TRight, TEdgeValue]: ...
    def limited_to(self, left: Set[TLeft], right: Set[TRight]) -> BipartiteGraph[TLeft, TRight, TEdgeValue]: ...

def enum_maximum_matchings_iter(graph: BipartiteGraph[TLeft, TRight, TEdgeValue]) -> Iterator[Dict[TLeft, TRight]]: ...