// represents 1 Server in a fixed-topology cluster
sig Node {
	id: disj one Int,
	neighbors: set Node,
}

abstract sig Distance {}
one sig Infinite extends Distance {}
sig Finite extends Distance {
	value: disj Int
}

sig DistanceEntry {
	id: disj one Int,
	var dist: Distance
}

fact allNodesHaveDistanceEntries {
	// every node must have a distance entry
	DistanceEntry.id = Node.id
}

pred update[du:Node, dv:Node] {
	//given a src/dest and the old and new possible distances between them, update src's distance "table" if new distance is better
	some dist1,dist2: Distance | { dist1.id = du.id and dist2.id = dv.id} => {
		(dist1 in Infinite and dist2 in Infinite) or (dist1 in Infinite and dist2 in Finite) =>
			
		(dist1 in Finite and dist2 in Infinite) =>
			
		(dist1 in Finite and dist2 in Finite) =>

	}
}

pred init {
	// initialize all DistanceEntry to be infinity, except for 1 "source" node with finite distance 0
	one n: Node | some f: Finite | some d: DistanceEntry | {
		// initialize 1 source node
		f.value = 0
		d.id = n.id
		d.dist = f

		// set all other DistanceEntry to be infinity
		(DistanceEntry - d).dist = Infinite
	}
}

fact graphContraints {
	neighbors = ~neighbors // undirected
	no iden & neighbors // no self loops
}

//pred canthave double dests
//
pred relax{
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

pred doNothingOnceFinished {

}

fact validTraces {
	init
 
	// for all nodes, keep relaxing
	// always( relax or doNothingOnceFinished) //or doNothing[n])
}

run {#Node = 3} for 3
