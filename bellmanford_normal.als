open util/integer
open util/boolean

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
//one sig UnitDistance extends Finite {} // dummy sig for distance addition

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
	Iter = sub[#Node, 1]
	Source.(Source.distances).value = 0 // Distance from the source to itself is zero (Finite)

	all n:(Node - Source) | {
		n->Infinite in Source.distances // initialize all Distances to Infinite
		one n.(Source.distances) // only one Distance per destination node
	}
}

fact graphContraints {
	neighbors = ~neighbors // undirected
	no iden & neighbors // no self loops
	all u, v:Node | u->v in ^neighbors // connected
}

//pred canthave double dests

pred relax{
	// precondition for for loop
	gt[Iter, 0]

	// action
	Iter' = sub[Iter, 1]

	// for all edge (u,v) in Edges
	all disj node1, node2: Node | (node1->node2 in neighbors and node2->node1 in neighbors) =>
		{
			let d_node1 = node1.(Source.distances) |
			{
			let d_node2 = node2.(Source.distances) |
			{
				lt[add[d_node1.value, 1], d_node2.value] => ( node2.(Source.distances').value = add[d_node1.value, 1] )
			}
			}
		}
	
}

// custom function to compare distances (which can be infinite)
//fun lessThanDistances[d1, d2: Distance] : Bool {
//	{
//		b:Bool | {
//			(d1 in Finite and d2 in Finite) => (b in lt[d1.value, d2.value])
//			(d1 in Finite and d2 in Infinite) => (b in True)
//			(d1 in Infinite and d2 in Finite) => (b in False)
//			(d1 in Infinite and d2 in Infinite) => (b in False)
//		}
//	}
//}

// define custom add Distances function
fun addDistances[d1, d2: Distance] : Distance {
	{
		d3:Distance | {
			(d1 in Finite and d2 in Finite) => (d3 in Finite and d3.value = add[d1.value, d2.value])
			not (d1 in Finite and d2 in Finite) => (d3 in Infinite)
		}
	}
}

pred doNothingOnceFinished {
	// pre condition
	Iter = 0
}

fact validTraces {
	init
 
	// addDistances[Source.(Source.distances), Source.(Source.distances)].value=0 // for testing addDistances

	// for all nodes, keep relaxing
	always( relax or doNothingOnceFinished ) //or doNothing[n])
}

run {#Node = 4} for 4
