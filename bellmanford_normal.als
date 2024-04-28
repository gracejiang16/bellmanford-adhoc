open util/integer
open util/boolean

// represents 1 Server in a fixed-topology cluster
sig Node {
	id: disj one Int,
	neighbors: set Node,
}

one sig Source extends Node {
	// SINGLE-source algorithm, so we specify a single source

	var distances : Node-> Distance
}

one var sig Iter in Int {} // for outer loop |v|-1 times

abstract sig Distance {}
one sig Infinite extends Distance {}
sig Finite extends Distance {
	value: disj Int
}

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
	all v: Node | {
		// for all nodes, if there should not be an update in the distance table (because there is no shorter path reachable), 
		// then the distance shouldn't change
      		(no u : Node | (u->v in neighbors and v->u in neighbors) and compareDistances[u.(Source.distances),v.(Source.distances)].isTrue)
         		=> v.(Source.distances') = v.(Source.distances)

		// for all nodes, if there should be an update in the distance table (because there is a shorter path reachable), 
		// then the distance should change
		some node2: Node | (v->node2 in neighbors and node2->v in neighbors) and
		{
			let d_node1 = node2.(Source.distances) |
			{
			let d_node2 = v.(Source.distances) |
			{
				compareDistances[d_node1,d_node2].isTrue => some f: Finite | {
					f.value = add[d_node1.value, 1] 
					node2.(Source.distances') = f
				}
			}
			}
		}
	}
}

// custom function to compare distances (which can be infinite)
// returns TRUE if d1+1 < d2
// NOTE: if d1 is Finite, we are comparing (d1 +1) to the value of d2 as opposed to strictly d1 < d2
fun compareDistances[d1, d2: Distance] : Bool {
	{
		b:Bool | {
			(d1 in Finite and d2 in Finite) => (lt[add[d1.value,1], d2.value] => b.isTrue)
			(d1 in Finite and d2 in Infinite) => (b.isTrue)
			(d1 in Infinite and d2 in Finite) => (b.isFalse)
			(d1 in Infinite and d2 in Infinite) => (b.isFalse)
		}
	}
}

pred doNothingOnceFinished {
	// pre condition
	Iter = 0

	// action
	distances' = distances
	Iter' = Iter
}

fact validTraces {
	init

	always( relax or doNothingOnceFinished )
}

run {#Node = 4} for 4
