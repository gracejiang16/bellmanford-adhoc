open util/boolean

// represents 1 Mobile Host, i.e., node in a wireless network
sig Node {
	id: disj one Int,
	neighbors: set Node,
	var distances : Node-> Distance,
	var state: State
}

abstract sig State {}
one sig Ready, Sent, Busy extends State{}

abstract sig Step{}
one sig Raise, Enter, Leave, Nothing extends Step{}

fact nodeMapsToOneDistance {
	// each node only maps to one distance
	always {
		all n, m: Node | one m.(n.distances)
	}
}

one var sig Iter in Int {} // to limit how many iterations we can do

abstract sig Distance {}
one sig Infinite extends Distance {}
sig Finite extends Distance {
	value: disj Int
}

pred init {
	Iter = add[#Node,#Node] // TODO increase if necessary
	all n:Node | {
		n.(n.distances).value = 0 // Distance from the source to itself is zero (Finite)
		n.state = Ready
	}

	all disj n, m:Node | {
		n->Infinite in m.distances // initialize all non self-to-self Distances to Infinite
		one n.(m.distances) // only one Distance per destination node
	}
}

fact graphContraints {
	neighbors = ~neighbors // undirected
	no iden & neighbors // no self loops
	all u, v:Node | u->v in ^neighbors // connected
}

// this pred is called whenever a node has new info in its distance table and needs to notify its neighbors
pred sendNewInfo {
	// precondition
	gt[Iter, 0]

	// action
	Iter' = sub[Iter, 1]

	// choose one node to update its neighbors' DV
	one sender: Node | {
		all neighbor: sender.neighbors | {
			//neighbor in sender.neighbors =>
			updateDV[sender, neighbor]
		}

		sender.state' = Sent  -- sender state only used to visualize which node is sending
		(Node - sender).state' = Ready
	}
}

// receiverNode updates its own distance vector (table) when it receives new info from sender
pred updateDV[sender:Node, receiver:Node]{
	// for all nodes, if there should be an update in the distance table (because there is a shorter path reachable through sender), 
		// then the distance should change
	all dest: Node |	
		{
		// if  there's shorter path to dest through sender, update own DV accordingly
		compareDistances[dest.(sender.distances), dest.(receiver.distances)].isTrue
		=> (some f: Finite | {
				f.value = add[dest.(sender.distances).value, 1]
				dest.(receiver.distances') = f
			}) // and sendNewInfo[receiver] // notify my neighbors that I updated my DV

		// if there's not shorter path to desk through sender, DV doesn't change
		compareDistances[dest.(sender.distances), dest.(receiver.distances)].isFalse
         	=> dest.(receiver.distances') = dest.(receiver.distances)
		}

	// distance vector of non-receiving nodes does not change
	all other: (Node - receiver) | other.distances' = other.distances
}

// custom function to compare distances (which can be infinite)
// returns TRUE if d1+1 < d2
// NOTE: if d1 is Finite, we are comparing (d1 +1) to the value of d2 as opposed to strictly d1 < d2
fun compareDistances[d1, d2: Distance] : Bool {
	{
		b:Bool | {
			(d1 in Finite and d2 in Finite and lt[add[d1.value,1], d2.value]) => (b.isTrue)
			(d1 in Finite and d2 in Finite and not lt[add[d1.value,1], d2.value]) => (b.isFalse)
			(d1 in Finite and d2 in Infinite) => (b.isTrue)
			(d1 in Infinite and d2 in Finite) => (b.isFalse)
			(d1 in Infinite and d2 in Infinite) => (b.isFalse)
		}
	}
}

pred doNothing {
	// pre condition
	Iter = 0

	// action
	distances' = distances
	state' = state
	

	//n.whichStep = Nothing
}

fact validTraces {
	init

	// always either sendNewInfo from one node or doNothing (when iter reaches 0)
	always {
		sendNewInfo or doNothing
	}
}

run {#Node = 3} for 3

---------------------------------------------

// once a distance between 2 nodes becomes finite, it can't revert back to infinite distance
assert staysFinite {
	always {
		all n, m : Node | (m.(n.distances) in Finite => once m.(n.distances) in Finite)
	}
}

check staysFinite

// the distance from a node to a node other than itself should always be non-zero
assert alwaysNonzeroDistanceToOtherNodes {
	always {
		all disj n, m : Node | (m.(n.distances) in Infinite or (m.(n.distances) in Finite and gt[(m.(n.distances).value), 0]))
	}
}

check alwaysNonzeroDistanceToOtherNodes
