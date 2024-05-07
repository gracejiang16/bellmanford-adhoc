# Modeling Bellman-Ford with Alloy
##### by Grace Jiang (gj101) and Karen Xiao (kx100)

## Installation:
This project is written in Alloy. All that is needed to run this project is alloy. Refer to the alloy documentation for download instructions: 
https://github.com/AlloyTools/org.alloytools.alloy/releases

## Overview:
Bellman-Ford (BF) is a single-source, shortest path algorithm. Given a starting node in a graph with edges of potentially differing weights, 
BF identifies the smallest cost paths to each other node. Using alloy, we model the iterative process of this algorithm. BF allows negative 
edge weights, unlike other shortest path algorithms such as Dijkstra’s, but does not alloy negative cycles. This project tackles the BF
algorithm within the context of ad hoc networks. Though the normal BF model can clearly be applied to find the distance from a single source
node to all other nodes in the graph, ad hoc networks require nodes to be able to calculate the shortest distance to other nodes. 
This is where the BF algorithm can be applied. The “catch” is that this version of BF is distributed and asynchronous, so there is no 
guarantee that each node will have the absolute shortest path to every other node at all times. So, our project tackles two main problems:
modeling the normal Bellman-Ford Algorithm and modeling the distributed (DSDV) Bellman-Ford Algorithm.

## Tradeoffs & Attempts:
### Normal BF Model
* For the ordinary BF model, we decided to omit the check for negative cycles. Though this is an important part of the normal BF algorithm,
  it doesn’t necessarily make sense in the context of ad hoc networks (which is our primary motivation for this assignment). 

### Distributed BF Model
* When attempting to model the distributed version of BF for ad hoc networks, we chose to limit the maximum number of “iterations” with an
  Iter variable. This is because the actual distributed BF does not ever end, given its ad hoc nature. 
* We also elected to model the distributed version with all edge weights equal to one. This is because, in a wireless cluster, the servers
  are most likely all identical so they have the same “radius” that they can reach.

## Scope & Limits:
We ran our model for up to 10 Nodes, but we assume that our model is correct for any arbitrary number of Nodes. Running on too many Nodes 
causes Alloy to be slow, so it is limiting and not feasible to run for a higher number of Nodes.

## Notes:
bellmanford_adhoc.als is not a currently working model. It contains some ideas we had that we didn’t have enough time to develop.
