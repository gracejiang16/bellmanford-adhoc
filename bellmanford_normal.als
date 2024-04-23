// represents 1 Server in a fixed-topology cluster
sig Node {
	id: disj one Int,
	//table: set TableRow,
	neighbors: set Node,
	var dests : set Node->Distance
}

abstract sig Distance {}
one sig Infinite extends Distance {}
sig Finite extends Distance {
	value: Int
}

pred update[src:Node, new_dist:Distance, old_dist:Distance] {
// given a src/dest and the old and new possible distances between them, update src's distance "table" if new distance is better
	(new_dist in Infinite and old_dist in Infinite) or (new_dist in Infinite and old_dist in Finite) =>
		(src.dests' = src.dests)
	(new_dist in Finite and old_dist in Infinite) =>
		(src.dests' = src.dests - src->old_dist + src->new_dist)

	(new_dist in Finite and old_dist in Finite) =>
		{ (new_dist.value < old_dist.value) =>
			(src.dests' = src.dests - src->old_dist + src->new_dist)
		  not (new_dist.value < old_dist.value) =>
			(src.dests' = src.dests)
		}
}

var sig toProcess in Node {} // set of nodes that still need to update their distance "tables"

pred init {
	all src:Node | src.dests = Node->Infinite
	toProcess = Node

	//all n:Node | some f:Finite | n->f in n.dests and f.value = 0// set distance to self as zero
}

fact graphContraints {
	neighbors = ~neighbors // undirected
	no iden & neighbors // no self loops
}

//pred canthave double dests

pred relax{
	// precondition
	some toProcess

	// action: choose one src to be processors
	one src: toProcess | 
	{
		//src.(src.dests) in Finite and src.(src.dests).value = 0 
		all neighbor : src.neighbors |
			{
				let dist_through_neighbor = neighbor.(src.dests) + 1 |
				{
				let dist_through_src = src.(src.dests) |
				{
					update[src, dist_through_neighbor, dist_through_src]
				}
				}
			}

		// below: dests don't change for non neighbors-of-src
		all nonNeighbor : Node - src.neighbors | nonNeighbor.dests' = nonNeighbor.dests	
		toProcess' = toProcess - src
	}

}

pred doNothingOnceFinished {
	// precondition
	no toProcess
	// action
	all n:Node | n.dests' = n.dests
	toProcess' = toProcess
}

fact validTraces {
	init 
	// for all nodes, keep relaxing
	always( relax or doNothingOnceFinished) //or doNothing[n])
}

run {#Node = 3} for 3
//Pred init
//Initialize distance to all other nodes as infinity
//#table = #Node // num of table rows must be total num Nodes minus 1
//pred updateTable[s: Node] // s is starting node
//all n : neighbors | s.Table.dest
