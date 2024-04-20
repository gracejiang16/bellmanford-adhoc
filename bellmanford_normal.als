// represents 1 Server in a fixed-topology cluster
sig Server {
	succ : one Server,
	id: Int,
	var distance : Int, // todo want a table with distance to every destination node

	var whichStep: Step
}

abstract sig Step{}
one sig SendPacket, Nothing extends Step{}
