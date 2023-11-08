package maf.cli.runnables

import maf.cli.runnables.AnalyzeWorklistAlgorithms.{numIterations, timeAnalysis, warmup, FIFOanalysis, LIFOanalysis}
import maf.core.{Address, Expression}
import maf.language.scheme.{SchemeExp, SchemeParser}
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scheme.modf.{
    SchemeModFComponent,
    SchemeModFKCallSiteSensitivity,
    SchemeModFNoSensitivity,
    SimpleSchemeModFAnalysis,
    StandardSchemeModFComponents
}
import maf.modular.{Dependency, DependencyTracking, GlobalStore, ModAnalysis}
import maf.modular.worklist.{
    LeastDependenciesFirstWorklistAlgorithm,
    PriorityQueueWorklistAlgorithm,
    RandomWorklistAlgorithm,
    SequentialWorklistAlgorithm
}
import maf.util.Reader
import maf.util.benchmarks.{Statistics, Timeout, Timer}
import maf.util.graph.{BellmanFord, FloydWarshall, Tarjan, TopSort}
import maf.util.Wrapper.instance
import maf.util.Wrapper2.instance

import java.io.File
import java.nio.file.{Files, Path, Paths}
import scala.collection.immutable.Set
import scala.collection.mutable
import scala.math.abs
import maf.util.datastructures.ListOps.*
import maf.util.benchmarks.Table
import maf.util.Writer
import maf.cli.experiments.worklist.ProgramGenerator
import maf.modular.*
import maf.util.MapUtil.invert

import java.io.ByteArrayInputStream

object DynamicWorklistAlgorithms:

    enum Priority: // prioritizing Least or Most Dependencies
        case Most, Least, Callee, Caller
    trait TopSort_AllDeps_POC[Expr <: Expression](priority: Priority) extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
        private var callDependencies: mutable.Map[Component, mutable.Set[Component]] = mutable.Map().withDefaultValue(mutable.Set.empty)

        // must first be called to provide the heuristic its perfect knowledge
        def updateDependencies(
                                  deps: mutable.Map[Component, mutable.Set[Component]],
                                  readDeps: Map[Component, Set[Address]],
                                  writeDeps: Map[Component, Set[Address]],
                              ): Unit =

            // adding read and write dependencies to the graph that is in DependencyTracking
            for {
                (reader, addresses) <- readDeps
                address <- addresses
                writer <- writeDeps.keys if writeDeps(writer)(address)
            } {
                addEdge(writer, reader)
            }

            // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
            // Care must be taken in case the graph consists of only 1 strongly connected component,
            // because in that case you actually get back a graph with only 1 node.
            val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)

            println(s"LENGTH: ${sccs.toList.length}")

            if sccs.toList.length == 1 then
                // code to only work with call dependencies
                callDependencies = deps
                deps.keySet.foreach(comp => {
                    val currDep = deps.getOrElse(comp, Set.empty)
                    depCount += (comp -> {
                        if priority == Priority.Least then
                            -currDep.size
                        else currDep.size
                    })
                })
                sccs.toList.length
            else {

                // applying topological sorting
                val sortedNodes = TopSort.topsort(sccs.toList, sccEdges)

                // updating the ordering of the priority queue based on the
                // number of dependencies
                sortedNodes.zipWithIndex.foreach { case (node, index) =>
                    sortedNodes.foreach(
                        // remarks:
                        // 1. all of the nodes of the same SCC get the same priority
                        // 2. last node of the topological sorting gets the highest priority (because has least call dependencies)
                        comps =>
                            comps.foreach(comp =>
                                depCount += (comp -> {
                                    if priority == Priority.Least then
                                        sortedNodes.length - index
                                    else index
                                })
                            )
                    )
                }
            }

    trait TopSort_CallDeps_POC[Expr <: Expression](priority: Priority)
        extends PriorityQueueWorklistAlgorithm[Expr]
            with DependencyTracking[Expr] :
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)

        def updateDependencies(
                                  deps: mutable.Map[Component, mutable.Set[Component]],
                                  readDeps: Map[Component, Set[Address]],
                                  writeDeps: Map[Component, Set[Address]]
                              ): Unit =
            graph = deps

            depCount = Map.empty.withDefaultValue(0)
            // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
            // Care must be taken in case the graph consists of only 1 strongly connected component,
            // because in that case you actually get back a graph with only 1 node.
            val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)

            // applying topological sorting
            val sortedNodes = TopSort.topsort(sccs.toList, sccEdges)

            // updating the ordering of the priority queue based on the
            // number of dependencies
            sortedNodes.zipWithIndex.foreach { case (comps, index) =>
                comps.foreach(comp =>
                    depCount += (comp -> {
                        if priority == Priority.Callee then
                            index
                        else sortedNodes.length - index
                    })
                )
            }


    trait TopSort_AllDeps_Live[Expr <: Expression](priority: Priority) extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)

        override def intraAnalysis(component: Component): LiveDependencyTrackingIntra
        trait LiveDependencyTrackingIntra extends DependencyTrackingIntra:
            override def commit(): Unit =
                super.commit()
                depCount = Map.empty.withDefaultValue(0)

                // adding read and write dependencies to the graph that is in DependencyTracking
                for {
                    (reader, addresses) <- readDependencies
                    address <- addresses
                    writer <- writeEffects.keys if writeEffects(writer)(address)
                } {
                    addEdge(writer, reader)
                }

                // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
                // Care must be taken in case the graph consists of only 1 strongly connected component,
                // because in that case you actually get back a graph with only 1 node.
                val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)

                if sccs.toList.length == 1 then
                // code to only work with call dependencies
                    dependencies.keySet.foreach(comp => {
                        val currDep = dependencies.getOrElse(comp, Set.empty)
                        depCount += (comp -> {
                            if priority == Priority.Least then
                                -currDep.size
                            else currDep.size
                        })
                    })
                else {

                    // applying topological sorting
                    val sortedNodes = TopSort.topsort(sccs.toList, sccEdges)

                    // updating the ordering of the priority queue based on the
                    // number of dependencies
                    sortedNodes.zipWithIndex.foreach { case (node, index) =>
                        sortedNodes.foreach(
                            // remarks:
                            // 1. all of the nodes of the same SCC get the same priority
                            // 2. last node of the topological sorting gets the highest priority (because has least call dependencies)
                            comps =>
                                comps.foreach(comp =>
                                    depCount += (comp -> {
                                        if priority == Priority.Least then
                                            sortedNodes.length - index
                                        else index
                                    })
                                )
                        )
                    }

                    // updating the ordering of the priority queue based on the
                    // number of dependencies
                }


    trait TopSort_CallDeps_Live_Without_Check[Expr <: Expression]
        extends PriorityQueueWorklistAlgorithm[Expr]
            with DependencyTracking[Expr] :
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)

        override def intraAnalysis(component: Component): LiveDependencyTrackingIntra

        trait LiveDependencyTrackingIntra extends DependencyTrackingIntra :

            override def commit(): Unit =
                super.commit()
                graph = dependencies
                depCount = Map.empty.withDefaultValue(0)
                // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
                // Care must be taken in case the graph consists of only 1 strongly connected component,
                // because in that case you actually get back a graph with only 1 node.
                val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)

                // applying topological sorting
                val sortedNodes = TopSort.topsort(sccs.toList, sccEdges)

                // println(s"sortedNodes: ${sortedNodes}")
                //     println(sortedNodes)

                // updating the ordering of the priority queue based on the
                // number of dependencies
                sortedNodes.zipWithIndex.foreach { case (comps, index) =>
                    comps.foreach(comp =>
                        depCount += (comp -> {
                            index
                        })
                    )
                }

    trait TopSort_CallDeps_Live_With_Check[Expr <: Expression](priority: Priority)
        extends PriorityQueueWorklistAlgorithm[Expr]
            with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
        var old_graph: mutable.Map[Component, mutable.Set[Component]] = mutable.Map()

        override def intraAnalysis(component: Component): LiveDependencyTrackingIntra

        trait LiveDependencyTrackingIntra extends DependencyTrackingIntra:

            override def commit(): Unit =
                super.commit()

                graph = dependencies

                if old_graph != graph then {
                    depCount = Map.empty.withDefaultValue(0)
                    old_graph = graph.clone()
                    // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
                    // Care must be taken in case the graph consists of only 1 strongly connected component,
                    // because in that case you actually get back a graph with only 1 node.
                    val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)

                    // applying topological sorting
                    val sortedNodes = TopSort.topsort(sccs.toList, sccEdges)

                    // println(s"sortedNodes: ${sortedNodes}")
                    //     println(sortedNodes)

                    // updating the ordering of the priority queue based on the
                    // number of dependencies
                    sortedNodes.zipWithIndex.foreach { case (comps, index) =>
                        comps.foreach(comp =>
                            depCount += (comp -> {
                                if priority == Priority.Callee then
                                    index
                                else sortedNodes.length - index
                            })
                        )
                    }
                }


    trait Main_Last_Heuristic[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr]:
        var depth: Map[Component, Int] = Map.empty.withDefaultValue(0) + (initialComponent -> -100)
        lazy val ordering: Ordering[Component] = Ordering.by(depth)(Ordering.Int)

    type Deps = mutable.Map[SchemeModFComponent, mutable.Set[SchemeModFComponent]]
    type GraphDeps = Map[SchemeModFComponent, Set[Address]]
    type SchemeAnalysisWithDeps = ModAnalysis[SchemeExp] with DependencyTracking[SchemeExp] with StandardSchemeModFComponents

    def runAnalysis[A <: SchemeAnalysisWithDeps](bench: (String, SchemeExp), analysis: SchemeExp => A): (Deps, GraphDeps, GraphDeps) =
        val a: A = analysis(bench._2)
        a.analyze()
        val dependencies: Deps = a.dependencies
        val readDependencies: GraphDeps = a.readDependencies
        val writeDependencies: GraphDeps = a.writeEffects
        (dependencies, readDependencies, writeDependencies)

    def randomAnalysis(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with RandomWorklistAlgorithm[SchemeExp] {

            val k = theK
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    // PROOF OF CONCEPT HEURISTICS
    def least_dependencies_first_POC(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with TopSort_AllDeps_POC[SchemeExp](Priority.Least) {
            val k = theK
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    def most_dependencies_first_POC(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with TopSort_AllDeps_POC[SchemeExp](Priority.Most) {
            val k = theK
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    def call_dependencies_only_POC(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with TopSort_CallDeps_POC[SchemeExp](Priority.Callee) {
            val k = theK

            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    // LIVE HEURISTICS

    def least_dependencies_first_Live(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with TopSort_AllDeps_Live[SchemeExp](Priority.Least) {
            val k = theK

            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with LiveDependencyTrackingIntra
        }

    def most_dependencies_first_Live(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with TopSort_AllDeps_Live[SchemeExp](Priority.Most) {
            val k = theK


            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with LiveDependencyTrackingIntra
        }

    def call_dependencies_only_Live_Without_Check(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with TopSort_CallDeps_Live_Without_Check[SchemeExp] {
            val k = theK

            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with LiveDependencyTrackingIntra
        }

    def call_dependencies_only_Live_With_Check(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with TopSort_CallDeps_Live_With_Check[SchemeExp](Priority.Callee) {
            val k = theK

            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with LiveDependencyTrackingIntra
        }


    def deprioritizeLargeInflow(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTrackingSnapshotAnalysis[SchemeExp]
            with PriorityQueueWorklistAlgorithm[SchemeExp] {
            val k = theK

            lazy val ordering: Ordering[Component] = Ordering.by(cmp => priorities(cmp))(Ordering.Int)
            private var priorities: Map[Component, Int] = Map().withDefaultValue(0)

            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingSnapshotIntra:
                    override def commit(): Unit =
                        super.commit()
                        priorities = readDependencies.invert.foldLeft(Map[Component, Int]().withDefaultValue(0)) { case (result, (adr, cmps)) =>
                            cmps.foldLeft(result)((result, cmp) =>
                                val count = dependencyTriggerCount.get(AddrDependency(adr)).getOrElse(0)
                                result.updatedWith(cmp)(v => Some(v.map(_ - count).getOrElse(-count)))
                            )
                        }
        }


    // Checks if adding an edge creates a cycle (by using BFS).
    def doesEdgeCreateCycle[Node,Component](graph: Map[Node, Set[Node]], from: Node, to: Node): Boolean = {
        val visited = mutable.Set[Node]()
        val queue = mutable.Queue[Node](to)

        while queue.nonEmpty do {
            val currentNode = queue.dequeue()
            if currentNode == from then
                return true // adding the edge would create a cycle

            visited += currentNode
            for (neighbor <- graph.getOrElse(currentNode, Set.empty) if !visited.contains(neighbor)) {
                queue.enqueue(neighbor)
            }
        }

        false // no cycle is introduced
    }

    /**
     * Experiment where components are prioritized where a large flow of values is orginating from, we do this by calculating the most expensive path
     * (in term of value flow) from each node to the nodes in the target node in the worklist. To this end, the flow edges are **reversed** such that
     * if there exists a flow from a -> b, the edge will be b -> a.
     */
    def gravitateInflow_with_Cycle_Check(distinguish: Boolean)(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTrackingSnapshotAnalysis[SchemeExp]
            with PriorityQueueWorklistAlgorithm[SchemeExp] {
            val k = theK

            // TODO: this is the same as the deprioritizeInflow, this should change
            lazy val ordering: Ordering[Component] = Ordering.by((cmp: Component) => priorities.getOrElse(cmp, 0.0))(Ordering.Double.TotalOrdering)
          //  lazy val ordering: Ordering[Component] = Ordering.by(priorities)(Ordering.Double.TotalOrdering)
            /** A map of edge weights corresponding to the number of triggers for that particular edge (inverted) */
            private var priorities: Map[Any, Double] = Map().withDefaultValue(0)

            /** A map that keeps track of the weights for an edge over time */
            private var weights: Map[(Node, Node), Double] = Map()

            /** A map that keeps track of all the write edges (= inverted writeEffects) */
            private var Ws: Map[Node, Set[Node]] = Map()

            var old_reads: Int = -1

            var old_writes: Int = -1


            enum Node:
                case AdrNode(adr: Address)
                case CmpNode(cmp: Component)

            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingSnapshotIntra:
                    override def commit(): Unit =
                        super.commit()
                        import FloydWarshall.*

                        given cats.Monoid[Double] with
                            def empty: Double = 0.0

                            def combine(x: Double, y: Double): Double = x + y

                        given Ordering[Double] = Ordering.Double.TotalOrdering


                        // the read dependencies make a flow from a component to an address possible
                        val Rs: Map[Node, Set[Node]] = readDependencies.map { case (k, v) => (Node.CmpNode(k) -> v.map(Node.AdrNode.apply)) }
                        // the write dependencies make a flow from an address to a component possible,
                        // however this is not how they are stored, so they have to be inverted
                        Ws = writeEffects.invert.foldLeft(Ws) { case (ws2, (from, tos)) =>
                            ws2 + (Node.AdrNode(from) -> tos.map(Node.CmpNode.apply))
                        }

                        if old_reads != Rs.size || old_writes != Ws.size then
                            old_reads = Rs.size
                            old_writes = Ws.size

                            // TODO: actually we will need the write and read dependencies to have a complete graph
                            // the read dependencies don't have to be inverted, but the write dependencies need
                            // to be inverted.

                            // the weights of the write edges correspond to the number of times they have been triggered,
                            // but with a reversed sign. This is to ensure that the shortest path chooses the edges
                            // with the smallest weight (thus the biggest flow) for its calculations.
                            weights = Ws.foldLeft(weights) { case (result, (from@Node.AdrNode(adr), tos)) =>
                                tos.foldLeft(result) { case (result, to@Node.CmpNode(comp)) => // all the components that write to this address
                                    val count: Double =
                                        if distinguish then
                                            dependencyTriggerCount_distinguish
                                              .get((AddrDependency(adr), comp))
                                              .map(_.toDouble).getOrElse(0.0) else
                                            dependencyTriggerCount
                                              .get(AddrDependency(adr))
                                              .map(_.toDouble)
                                              .getOrElse(0.0)
                                    result.updatedWith((from, to))(v => Some(v.map(_ - count).getOrElse(-count)))
                                    // ^ updating weight of the edge adr -> comp (where comp writes to adr)
                                }
                            }
                            // set the read edges to 0
                            weights = forallEdges(Rs).foldLeft(weights) { case (result, (from, to)) =>
                                result.updated((from, to), 0)
                            }

                            // initializing the edges and nodes as empty
                            var edges: Map[Node, Set[Node]] = Map.empty
                            var nodes: Set[Node] = Set.empty

                            // adding all write edges at once
                            for ((from, toSet) <- writeEffects.invert) {
                                val fromNode = Node.AdrNode(from)
                                val toNodes = toSet.map(Node.CmpNode.apply)

                                edges += fromNode -> toNodes
                                nodes += fromNode
                                nodes ++= toNodes
                            }

                            // processing read dependencies one by one, checking for cycles
                            // only adding the edge if no cycle is introduced
                            for ((from, toSet) <- readDependencies) do {
                                val fromNode = Node.CmpNode(from)
                                val toNodes = toSet.map(Node.AdrNode.apply)

                                for (toNode <- toNodes) {
                                    if !doesEdgeCreateCycle[Node,Component](edges,fromNode,toNode) then {
                                        edges += fromNode -> (edges.getOrElse(fromNode, Set.empty) + toNode)
                                        nodes += fromNode
                                        nodes += toNode
                                    }
                                }
                            }


                            // compute the "heaviest" component, that is, accumulate all paths
                            // that end with this node, and sum their maximal weight together,
                            // then we compute priority over that
                            val floydwarshallWeights = FloydWarshall.floydwarshall(nodes, edges, weights, Double.PositiveInfinity)
                            priorities = nodes
                                .map(destination =>
                                    destination -> nodes // realise that we have '->' here, which means that we construct a pair
                                        .flatMap(source => floydwarshallWeights.get((source, destination)).map(Math.abs))
                                        .foldLeft(0.0)(_ + _)
                                )
                                .toMap

                           // val (sccs, sccEdges) = Tarjan.collapse(nodes, edges)
                           // val hasNegativeCycle = BellmanFord.hasNegativeCycle(nodes, edges, weights, Double.PositiveInfinity)

    //                        println(s"NUMBER OF NODES: ${nodes.toList.length}")
    //                        println(s"NUMBER OF SCCS: ${sccs.toList.length}")
    //                        println(s"HAS NEGATIVE CYCLES: ${hasNegativeCycle}")
    //                        println(s"MAX WEIGHT: ${weights.values.max}")
    //                        println(s"MIN WEIGHT: ${weights.values.min}")
    //                        println(s"MAX Floyd Warshall WEIGHT: ${floydwarshallWeights.values.max}")
    //                        println(s"MIN Floyd Warshall WEIGHT: ${floydwarshallWeights.values.min}")
    //                        println(s"MAX PRIORITY: ${priorities.values.max}")
    //                        println(s"MIN PRIORITY: ${priorities.values.min}")

                            val edgesDot: Map[String, Set[String]] = edges.map { case (k, v) =>
                                (k.toString, v.map(_.toString()))
                            }
                            val dot = VisualizeTriggers.toDot(edgesDot, weights.map { case ((from, to), v) => (from.toString(), v.toInt) }.toMap)

                            import scala.sys.process.*
                            ((s"sfdp -x -Goverlap=scale -Tpdf -o /tmp/frame-final.pdf") #< ByteArrayInputStream(dot.getBytes())).!!

        }

    /**
     * Experiment where components are prioritized where a large flow of values is orginating from, we do this by calculating the most expensive path
     * (in term of value flow) from each node to the nodes in the target node in the worklist. To this end, the flow edges are **reversed** such that
     * if there exists a flow from a -> b, the edge will be b -> a.
     */
    def gravitateInflow(distinguish: Boolean)(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTrackingSnapshotAnalysis[SchemeExp]
            with PriorityQueueWorklistAlgorithm[SchemeExp] {
            val k = theK

            // TODO: this is the same as the deprioritizeInflow, this should change
            lazy val ordering: Ordering[Component] = Ordering.by((cmp: Component) => priorities.getOrElse(cmp, 0.0))(Ordering.Double.TotalOrdering)

            /** A map of edge weights corresponding to the number of triggers for that particular edge (inverted) */
            private var priorities: Map[Any, Double] = Map().withDefaultValue(0)

            /** A map that keeps track of the weights for an edge over time */
            private var weights: Map[(Node, Node), Double] = Map()

            /** A map that keeps track of all the write edges (= inverted writeEffects) */
            private var Ws: Map[Node, Set[Node]] = Map()

            enum Node:
                case AdrNode(adr: Address)
                case CmpNode(cmp: Component)

            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingSnapshotIntra:
                    override def commit(): Unit =
                        super.commit()
                        import FloydWarshall.*

                        given cats.Monoid[Double] with
                            def empty: Double = 0.0
                            def combine(x: Double, y: Double): Double = x + y

                        given Ordering[Double] = Ordering.Double.TotalOrdering


                        // TODO: actually we will need the write and read dependencies to have a complete graph
                        // the read dependencies don't have to be inverted, but the write dependencies need
                        // to be inverted.

                        // the read dependencies make a flow from a component to an address possible
                        val Rs: Map[Node, Set[Node]] = readDependencies.map { case (k, v) => (Node.CmpNode(k) -> v.map(Node.AdrNode.apply)) }
                        // the write dependencies make a flow from an address to a component possible,
                        // however this is not how they are stored, so they have to be inverted
                        Ws = writeEffects.invert.foldLeft(Ws) { case (ws2, (from, tos)) =>
                            ws2 + (Node.AdrNode(from) -> tos.map(Node.CmpNode.apply))
                        }
                        // the weights of the write edges correspond to the number of times they have been triggered,
                        // but with a reversed sign. This is to ensure that the shortest path chooses the edges
                        // with the smallest weight (thus the biggest flow) for its calculations.
                        weights = Ws.foldLeft(weights) { case (result, (from @ Node.AdrNode(adr), tos)) =>
                            tos.foldLeft(result) { case (result, to@Node.CmpNode(comp)) => // all the components that write to this address
                                val count: Double =
                                    if distinguish then
                                        dependencyTriggerCount_distinguish
                                          .get((AddrDependency(adr), comp))
                                          .map(_.toDouble).getOrElse(0.0) else
                                        dependencyTriggerCount
                                          .get(AddrDependency(adr))
                                          .map(_.toDouble)
                                          .getOrElse(0.0)
                                result.updatedWith((from, to))(v => Some(v.map(_ - count).getOrElse(-count)))
                                // ^ updating weight of the edge adr -> comp (where comp writes to adr)
                            }
                        }
                        // set the read edges to 0
                        weights = forallEdges(Rs).foldLeft(weights) { case (result, (from, to)) =>
                            result.updated((from, to), 0)
                        }

                        val edges: Map[Node, Set[Node]] = (Rs.toSeq ++ Ws.toSeq).groupBy(_._1).view.mapValues(d => d.flatMap(_._2).toSet).toMap


                        // the nodes are all nodes that participate in the Rs and Ws edge sets
                        // forallEdges transforms (from, tos) to ((from,to_1), (from,to_2), ...)
                        val nodes = (forallEdges(Rs) ++ forallEdges(Ws)).flatMap { case (n1, n2) => List(n1, n2) }.toSet

                        // compute the "heaviest" component, that is, accumulate all paths
                        // that end with this node, and sum their maximal weight together,
                        // then we compute priority over that
                        val floydwarshallWeights = FloydWarshall.floydwarshall(nodes, edges, weights, Double.PositiveInfinity)
                        priorities = nodes
                            .map(destination =>
                                destination -> nodes // realise that we have '->' here, which means that we construct a pair
                                    .flatMap(source => floydwarshallWeights.get((source, destination)).map(Math.abs))
                                    .foldLeft(0.0)(_ + _)
                            )
                            .toMap

                        val edgesDot: Map[String, Set[String]] = edges.map { case (k, v) =>
                            (k.toString, v.map(_.toString()))
                        }
                        val dot = VisualizeTriggers.toDot(edgesDot, weights.map { case ((from, to), v) => (from.toString(), v.toInt) }.toMap)

                        import scala.sys.process.*
                        ((s"sfdp -x -Goverlap=scale -Tpdf -o /tmp/frame-final.pdf") #< ByteArrayInputStream(dot.getBytes())).!!

        }

    def fairness(theK: Int)(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFKCallSiteSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with PriorityQueueWorklistAlgorithm[SchemeExp] {
            val k = theK

            lazy val ordering: Ordering[Component] = Ordering.by(cmp => counts(cmp))(Ordering.Int)
            private var counts: Map[Component, Int] = Map().withDefaultValue(0)

            override def intraAnalysis(cmp: SchemeModFComponent) =
                counts = counts.updatedWith(cmp)(v => Some(v.getOrElse(0) - 1))
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    val analyses = List(
        ("random", randomAnalysis),
        ("FIFO", FIFOanalysis),
        ("LIFO", LIFOanalysis),
        ("INFLOW", deprioritizeLargeInflow),
        ("FAIR", fairness),
        ("INFLOW'", gravitateInflow(false)),
        ("INFLOW'_Distinguish", gravitateInflow(true)),
        ("INFLOW'_WITH_CYCLE_CHECK", gravitateInflow_with_Cycle_Check(false)),
        ("INFLOW'_WITH_CYCLE_CHECK_Distinguish", gravitateInflow_with_Cycle_Check(true))
    )

    type Analysis = SimpleSchemeModFAnalysis & DependencyTracking[SchemeExp]

    def benchmark(
                     bench: Map[String, String],
                     analyses: List[(String, Int => SchemeExp => Analysis)]
                 )(
                     output: String,
                     loadFile: (String => String) = Reader.loadFile
                 ): Unit =
        var outputTable: Table[Option[Double]] = Table.empty(default = None)
        bench.toList
            .cartesian(analyses)
            .cartesian((0 until 1).toList)
            .foreach { case (((filename, name), (analysisType, makeAnalysis)), k) =>
                print(s"Analyzing $name with $analysisType with k=$k")
                val program = SchemeParser.parseProgram(loadFile(filename))


                val anl = makeAnalysis(k)(program)
                val result = timeAnalysis((name, program), anl, analysisType).map { case (result, timeTaken) =>
                    (result.totalIterations.toDouble, timeTaken / (1000 * 1000), result.totalVarSize.toDouble, result.totalRetSize.toDouble)
                }
                println()
                println(s"NUMBER OF INTRA-ANALYSES: ${anl.num_analyses}")

/*                // Run
                val results: Option[List[(Double, Double, Double, Double)]] = (1 to (warmup + numIterations)).toList
                    .mapM(i =>
                        print(i)
                        val anl = makeAnalysis(k)(program)
                        val result = timeAnalysis((name, program), anl, analysisType).map { case (result, timeTaken) =>
                            (result.totalIterations.toDouble, timeTaken / (1000 * 1000), result.totalVarSize.toDouble, result.totalRetSize.toDouble)
                        }
                        println(s"NUMBER OF INTRA-ANALYSES: ${anl.num_analyses}")
                        result
                    )
                    .map(_.drop(warmup))*/

                println()

/*                // Compute metrics
                if results.isDefined then
                    val stats = Statistics.all(results.get.map(_._2).toList)
                    outputTable = outputTable.add(s"${name}%%$analysisType%%$k", "time_mean", Some(stats.mean))
                    outputTable = outputTable.add(s"${name}%%$analysisType%%$k", "time_stdev", Some(stats.stddev))
                    outputTable = outputTable.add(s"${name}%%$analysisType%%$k", "time_median", Some(stats.median))
                    outputTable = outputTable.add(s"${name}%%$analysisType%%$k", "# iterations", Some(results.get.head._1))
                    outputTable = outputTable.add(s"${name}%%$analysisType%%$k", "var size", Some(results.get.head._3))
                    outputTable = outputTable.add(s"${name}%%$analysisType%%$k", "ret size", Some(results.get.head._4))
                else outputTable = outputTable.add(s"${name}%%$analysisType%%$k", "time_mean", None)

                // Construct the output table and flush the output table to a file
                val outputString = outputTable.toCSVString(format = {
                    case Some(v) => v.toString
                    case None    => "TIMEOUT"
                })

                val file = Writer.open("output/results.csv")
                Writer.write(file, outputString)
                Writer.close(file)*/
            }

    abstract class BenchmarkSuite:
        val benchmarks: Map[String, String]
        def load(name: String): String

    case class RealWorld(benchmarks: Map[String, String]) extends BenchmarkSuite:
        def load(name: String): String = Reader.loadFile(name)

    case class Synthetic(benchmarks: Map[String, String]) extends BenchmarkSuite:
        def load(name: String): String = name

    lazy val suites: Map[String, BenchmarkSuite] = Map(
        "all" -> RealWorld(bench),
        "synthetic" -> Synthetic(synth),
    ) ++ (bench.map { case (k, v) => v -> RealWorld(Map(k -> v)) })

    private lazy val synth: Map[String, String] =
        // Generate inflow1 programs with varying number of components
        val upflow1s = List() // (1 to 100).map(i => (ProgramGenerator.upflow(i), "upflow1%%" + (i.toString)))
        val upflow2s = (6 to 6).map(i => (ProgramGenerator.upflow2(i), "upflow2%%" + (i.toString)))
        (upflow1s ++ upflow2s).toMap

    private lazy val bench: Map[String, String] = List(
        ("test/R5RS/gambit/scheme.scm", "scheme"),
        ("test/R5RS/icp/icp_7_eceval.scm", "eceval"),
        ("test/R5RS/icp/icp_1c_multiple-dwelling.scm", "multiple-dwelling"),
        ("test/R5RS/gambit/sboyer.scm", "sboyer"),
        ("test/R5RS/gambit/peval.scm", "peval"),
        ("test/R5RS/icp/icp_1c_prime-sum-pair.scm", "prime-sum-pair"),
        ("test/R5RS/WeiChenRompf2019/toplas98/boyer.scm", "boyer"),
        ("test/R5RS/various/SICP-compiler.scm", "SICP-compiler"),
        ("test/R5RS/icp/icp_8_compiler.scm", "compiler"),
        ("test/R5RS/scp1/family-budget.scm", "family-budget"),
        ("test/R5RS/scp1/draw-umbrella.scm", "draw-umbrella"),
        // Gabriel
        ("test/R5RS/gabriel/triangl.scm", "triangl"),
        ("test/R5RS/gabriel/browse.scm", "browse"),
        ("test/R5RS/gabriel/diviter.scm", "diviter"),
        ("test/R5RS/gabriel/cpstak.scm", "cpstak"),
        ("test/R5RS/gabriel/divrec.scm", "divrec"),
        ("test/R5RS/gabriel/dderiv.scm", "dderiv"),
        ("test/R5RS/gabriel/destruc.scm", "destruct"),
        ("test/R5RS/gabriel/deriv.scm", "deriv"),
        ("test/R5RS/gabriel/takl.scm", "takl"),
        ("test/R5RS/gabriel/puzzle.scm", "puzzle"),
        // Other
        //("test/R5RS/VUB-projects/railway-control-system.scm", "railway-control-system"),
        //("test/R5RS/VUB-projects/frogger.scm", "frogger"),
        ("test/R5RS/various/pico.scm", "pico"),
        //("test/R5RS/github/google-schism.scm", "google-schism"),
        ("test/R5RS/gambit/matrix.scm", "matrix"),
        ("test/R5RS/icp/icp_1c_prime-sum-pair.scm", "icp_1c_prime-sum-pair")
    ).toMap

    private lazy val synth_arman: Map[String, String] =
        Map(ProgramGenerator.upflow2(3) -> "upflow_arman")

    lazy val suites_arman: Map[String, BenchmarkSuite] = Map(
        "synthetic" -> Synthetic(synth_arman),
    )

    def main(args: Array[String]): Unit =

        suites.values.foreach { suite =>
            benchmark(suite.benchmarks, analyses)(s"output/${suite}_out.csv", suite.load)
        }

/*if args.isEmpty then println("No benchmark suites to execute")
else
    val found = args.filter(name => !suites.contains(name))
    if found.length > 0 then println(s"Could not find the following benchmark suites: ${found.mkString(",")}")
    else
        args.foreach { arg =>
            val suite = suites(arg)
            benchmark(suite.benchmarks, analyses)(s"output/${arg}_out.csv", suite.load)
        }*/
