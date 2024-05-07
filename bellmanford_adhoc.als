open util/boolean

// represents 1 Mobile Host, i.e., node in a wireless network
sig Node {
	id: disj one Int,
	neighbors: set Node,
	var distances : Node-> Distance,

	var whichStep: Step
}

abstract sig State {}
one sig Uninterested, Waiting, Busy extends State{}

abstract sig Step{}
one sig Raise, Enter, Leave, Nothing extends Step{}

fact nodeMapsToOneDistance {
	// each node only maps to one distance
	always {
		all n, m: Node | one m.(n.distances)
	}
}

fact staysFinite {
	// once a distance between 2 nodes becomes finite, it can't revert back to infinite distance
	always {
		all n, m : Node | (m.(n.distances) in Finite => once m.(n.distances) in Finite)
	}
}

one var sig Iter in Int {} // to limit how many iterations we can do

abstract sig Distance {}
one sig Infinite extends Distance {}
sig Finite extends Distance {
	value: disj Int
}

pred init {
	Iter = #Node // TODO increase if necessary
	all n:Node | n.(n.distances).value = 0 // Distance from the source to itself is zero (Finite)

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
pred sendNewInfo[sender: Node] {
	// precondition
	gt[Iter, 0]

	// action
	Iter' = sub[Iter, 1]

	all neighbor: sender.neighbors | updateDV[sender, neighbor]

//	sender.whichStep = SendInfo
}

// receiverNode updates its own distance vector (table) when it receives new info from sender
pred updateDV[sender:Node, receiver:Node]{
	// if there's not shorter path to desk through sender, DV doesn't change
      	(no dest: Node | compareDistances[dest.(sender.distances), dest.(receiver.distances)].isTrue)
         	=> receiver.distances' = receiver.distances

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
		}
	//receiver.whichStep = Update
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

pred doesNothing[n:Node] {
	// pre condition
	Iter = 0

	// action
	n.distances' = n.distances

	n.whichStep = Nothing
}

fact validTraces {
	init

	all n:Node | sendNewInfo[n] // algo starts by all Nodes sending their own distance tables

	always {
		all n: Node | sendNewInfo[n] or doesNothing[n]
	}
}

run {#Node = 5} for 5

