import sys
import networkx as nx


if sys.version_info[0:2] > (3, 6):
    OrderedDiGraph = nx.DiGraph
    OrderedGraph = nx.Graph
else:
    OrderedDiGraph = nx.OrderedDiGraph
    OrderedGraph = nx.OrderedGraph
