open util/boolean

// represents 1 Server in a fixed-topology cluster
sig Node {
	id: disj one Int,
	neighbors: set Node,

	weights : Node->Finite
}

// there must be weights between neighbor pairs that are positive (in our implementation) and finite
fact weightsBetweenNeighborPairs {
	all disj n, m : Node | (m in n.neighbors) // if n and m are neighbors
		=> (some d : Finite | m->d in n.weights and gt[d.value, 0]) // then n to m has some positive finite edge weight
}

one sig Source extends Node {
	// SINGLE-source algorithm, so we specify a single source
	var distances : Node-> Distance
}

fact nodeMapsToOneDistanceAndWeight {
	// each node only maps to one distance
	always {
		all n: Node | one n.(Source.distances)
	}

	// each node pair only has one weight
	always {
		all n, m : Node | one m.(n.weights)
	}
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
	}
}

fact graphContraints {
	no iden & neighbors // no self loops
	all u, v:Node | u->v in ^neighbors // connected
}

pred relax{
	// precondition for for loop
	gt[Iter, 0]

	// action
	Iter' = sub[Iter, 1]

	// for all edge (u,v) in Edges
	all v: Node | {
		// for all nodes, if there should not be an update in the distance table (because there is no shorter path reachable), 
		// then the distance shouldn't change
      		(no u1: Node | (u1->v in neighbors) and compareDistances[addDistances[u1.(Source.distances), v.(u1.weights)], v.(Source.distances)].isTrue)
         		=> v.(Source.distances') = v.(Source.distances)

		// for all nodes, if there should be an update in the distance table (because there is a shorter path reachable), 
		// then the distance should change
		all u2: Node | (u2->v in neighbors) and compareDistances[addDistances[u2.(Source.distances), v.(u2.weights)], v.(Source.distances)].isTrue
			=> some f: Finite | {
					f.value = (addDistances[u2.(Source.distances), v.(u2.weights)]).value
					v.(Source.distances') = f
				}
	}
}

// define custom add Distances function
fun addDistances[d1, d2: Distance] : Distance {
	{
		d3:Distance | {
			(d1 in Finite and d2 in Finite) => (d3 in Finite and d3.value = add[d1.value, d2.value])
			not (d1 in Finite and d2 in Finite) => (d3 in Infinite)
		}
	}
}

// custom function to compare distances (which can be infinite)
// returns TRUE if d1< d2
fun compareDistances[d1, d2: Distance] : Bool {
	{
		b:Bool | {
			(d1 in Finite and d2 in Finite and lt[d1.value, d2.value]) => (b.isTrue)
			(d1 in Finite and d2 in Finite and not lt[d1.value, d2.value]) => (b.isFalse)
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

run {#Node = 5} for 5

// check that no shorter path exists to every node
assert foundShortestPaths {
	eventually {
		all dest: Node | { // for all destination nodes,
			no edges: set Node->Node { // there isn't another smaller cost path from Source
				(Source->dest in ^edges) and lt[sum[(Node.edges).((edges.Node).distances).value], dest.(Source.distances).value]
			}
		}
	}
}
check foundShortestPaths

// once a distance between 2 nodes becomes finite, it can't revert back to infinite distance
assert staysFinite {
	always {
		all n: Node | (n.(Source.distances) in Finite => once n.(Source.distances) in Finite)
	}
}

check staysFinite
