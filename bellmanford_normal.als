// represents 1 Server in a fixed-topology cluster
sig Node {
	id: disj one Int,
	table: set TableRow,
	//whichStep,
	neighbors: set Node
}

fact graphContraints {
	neighbors = ~neighbors // undirected
	no iden & neighbors // no self loops
}

sig TableRow {
	source: one Node,
	dest: one Node,
	distance: one Int
}

fact completeTable {
	// ensure every Node pair has an entry in TableRow table
	all src : Node | #(src.table) = #Node //  #(src.~source) = #Node
}

//pred init {
//	Initialize distance to all other nodes as infinity
//	all n: Node | n.table. // num table rows must = num Nodes
//}

run {#Node = 4} for 4
//Pred init
//Initialize distance to all other nodes as infinity
//#table = #Node // num of table rows must be total num Nodes minus 1
//pred updateTable[s: Node] // s is starting node
//all n : neighbors | s.Table.dest
