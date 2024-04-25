open util/integer

// represents 1 Server in a fixed-topology cluster
sig Node {
	id: disj one Int,
	neighbors: set Node,
}

one sig Source extends Node {
	// SINGLE-source algorithm, so we specify a single source

	var distances : Node->Distance
}

one var sig Iter in Int {} // for outer loop |v|-1 times

abstract sig Distance {}
one sig Infinite extends Distance {}
sig Finite extends Distance {
	value: disj Int
}

//pred update[du:Node, dv:Node] {
//	//given a src/dest and the old and new possible distances between them, update src's distance "table" if new distance is better
//	some dist1,dist2: Distance | { dist1.id = du.id and dist2.id = dv.id} => {
//		(dist1 in Infinite and dist2 in Infinite) or (dist1 in Infinite and dist2 in Finite) =>
//			
//		(dist1 in Finite and dist2 in Infinite) =>
//			
//		(dist1 in Finite and dist2 in Finite) =>
//
//	}
//}

pred init {
	Source.(Source.distances).value = 0 // Distance from the source to itself is zero (Finite)

	all n:(Node - Source) | {
		n->Infinite in Source.distances // initialize all Distances to Infinite
		one n.(Source.distances) // only one Distance per destination node
	}
}

fact graphContraints {
	neighbors = ~neighbors // undirected
	no iden & neighbors // no self loops
}

//pred canthave double dests

pred relax{
	// precondition for for loop
	gt[Iter, 0]

	// action
	Iter' = sub[Iter, 1]
	// for all edge (u,v) in Edges
	all neighbor: neighbors |
		{
			let dist_u = neighbor.Node --
			{
				let dist_v = Node.neighbor |
				{
					update[dist_u, dist_v]
				}
			}
		}

	// below: dests don't change for non neighbors-of-src
	//all nonNeighbor : Node - src.neighbors | nonNeighbor.dests' = nonNeighbor.dests	
	
}

fun addDistances[d1, d2: Distance] : Dist {
	some d3:Distance | {
		d1 in Infinite or d2 in Infinite | some Infinite
	}
}

pred doNothingOnceFinished {
	
}

fact validTraces {
	init
 
	// for all nodes, keep relaxing
	// always( relax or doNothingOnceFinished) //or doNothing[n])
}

run {#Node = 4} for 4
