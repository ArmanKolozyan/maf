package maf.cli.runnables

import maf.cli.runnables.AnalyzeWorklistAlgorithms.{numIterations, timeAnalysis, warmup, FIFOanalysis, LIFOanalysis}
import maf.cli.runnables.DynamicWorklistAlgorithms.{
    LeastDependenciesFirstWorklistAlgorithmPOC,
    LiveLeastDependenciesFirstWorklistAlgorithm,
    LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_With_Check2
}
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
import maf.util.graph.{Tarjan, TopSort}
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

object DynamicWorklistAlgorithms extends App:

    trait LeastDependenciesFirstWorklistAlgorithmPOC[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
        private var callDependencies: mutable.Map[Component, mutable.Set[Component]] = mutable.Map().withDefaultValue(mutable.Set.empty)

        def updateDependencies(
            deps: mutable.Map[Component, mutable.Set[Component]],
            readDeps: Map[Component, Set[Address]],
            writeDeps: Map[Component, Set[Address]]
          ): Int =

            // adding read and write dependencies to the graph that is in DependencyTracking
            for {
                (reader, addresses) <- readDeps
                address <- addresses
                writer <- writeDeps.keys if writeDeps(writer)(address)
            } {
                addEdge(writer, reader)
            }

            // a graph to test how Tarjan.collapse works
            val test_graph = Map("a" -> Set("b"), "b" -> Set("c"), "c" -> Set("d"), "d" -> Set("a"))

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
                    depCount += (comp -> -currDep.size)
                })
                return sccs.toList.length
            else {

                /// Now we are going to construct a new graph that has as
                /// nodes the strongly connected components of the original graph

                // a map from the new graph nodes to the original graph nodes
                val newToOrigNodes: Map[String, Set[Component]] = sccs.zipWithIndex.map { case (nodes, idx) =>
                    val newNode = s"node$idx"
                    newNode -> nodes
                }.toMap

                // constructing the new graph
                val newGraph: Map[String, Set[String]] = sccEdges.map { case (from, tos) =>
                    val fromNode = newToOrigNodes.find(_._2 == from).map(_._1).get
                    val toNodes = tos.flatMap(t => newToOrigNodes.find(_._2 == t).map(_._1))
                    fromNode -> toNodes
                }

                // applying topological sorting
                val sortedNodes = TopSort.topsort(newGraph.keys.toList, newGraph)

                // updating the ordering of the priority queue based on the topological order
                sortedNodes.zipWithIndex.foreach { case (node, index) =>
                    newToOrigNodes
                        .get(node)
                        .get
                        .foreach(
                          // remarks:
                          // 1. all of the nodes of the same SCC get the same priority
                          // 2. first node of the topological sorting gets the highest priority (because has least dependencies)
                          comp =>
                              depCount += (comp -> {
                                  sortedNodes.length - index
                              })
                        )
                }
                return sccs.toList.length
            }

    trait LiveLeastDependenciesFirstWorklistAlgorithm[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr]:
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

                // a graph to test how Tarjan.collapse works
                val test_graph = Map("a" -> Set("b"), "b" -> Set("c"), "c" -> Set("d"), "d" -> Set("a"))

                // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
                // Care must be taken in case the graph consists of only 1 strongly connected component,
                // because in that case you actually get back a graph with only 1 node.
                val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)

                if sccs.toList.length == 1 then
                    // code to only work with call dependencies
                    dependencies.keySet.foreach(comp => {
                        val currDep = dependencies.getOrElse(comp, Set.empty)
                        depCount += (comp -> -currDep.size)
                    })
                else {

                    /// Now we are going to construct a new graph that has as
                    /// nodes the strongly connected components of the original graph

                    // a map from the new graph nodes to the original graph nodes
                    val newToOrigNodes: Map[String, Set[Component]] = sccs.zipWithIndex.map { case (nodes, idx) =>
                        val newNode = s"node$idx"
                        newNode -> nodes
                    }.toMap

                    // constructing the new graph
                    val newGraph: Map[String, Set[String]] = sccEdges.map { case (from, tos) =>
                        val fromNode = newToOrigNodes.find(_._2 == from).map(_._1).get
                        val toNodes = tos.flatMap(t => newToOrigNodes.find(_._2 == t).map(_._1))
                        fromNode -> toNodes
                    }

                    // applying topological sorting
                    val sortedNodes = TopSort.topsort(newGraph.keys.toList, newGraph)

                    // updating the ordering of the priority queue based on the
                    // number of dependencies
                    sortedNodes.zipWithIndex.foreach { case (node, index) =>
                        newToOrigNodes
                            .get(node)
                            .get
                            .foreach(
                              // remarks:
                              // 1. all of the nodes of the same SCC get the same priority
                              // 2. first node of the topological sorting gets the highest priority (because has least dependencies)
                              comp =>
                                  depCount += (comp -> {
                                      sortedNodes.length - index
                                  })
                            )
                    }
                }

    def mySum[T](list: List[T])(implicit num: Numeric[T]): T = {
        list.foldLeft(num.zero)(num.plus)
    }

    trait LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_With_Check[Expr <: Expression]
        extends PriorityQueueWorklistAlgorithm[Expr]
        with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
        var old_graph: mutable.Map[Component, mutable.Set[Component]] = mutable.Map()

        override def intraAnalysis(component: Component): LiveDependencyTrackingIntra

        trait LiveDependencyTrackingIntra extends DependencyTrackingIntra:

            override def commit(): Unit =
                super.commit()
                depCount = Map.empty.withDefaultValue(0)

                graph = dependencies

                if old_graph != graph then {
                    old_graph = graph.clone()
                    // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
                    // Care must be taken in case the graph consists of only 1 strongly connected component,
                    // because in that case you actually get back a graph with only 1 node.
                    val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)

                    /// Now we are going to construct a new graph that has as
                    /// nodes the strongly connected components of the original graph

                    // a map from the new graph nodes to the original graph nodes
                    val newToOrigNodes: Map[Int, Set[Component]] = sccs.zipWithIndex.map { case (nodes, idx) =>
                        val newNode = idx
                        newNode -> nodes
                    }.toMap

                    // constructing the new graph
                    val newGraph: Map[Int, Set[Int]] = sccEdges.map { case (from, tos) =>
                        val fromNode = newToOrigNodes.find(_._2 == from).map(_._1).get
                        val toNodes = tos.flatMap(t => newToOrigNodes.find(_._2 == t).map(_._1))
                        fromNode -> toNodes
                    }

                    // applying topological sorting
                    val sortedNodes = TopSort.topsort(sccs.toList, sccEdges)

                    // updating the ordering of the priority queue based on the
                    // number of dependencies
                    sortedNodes.zipWithIndex.foreach { case (node, index) =>
                        sortedNodes.foreach(
                          // remarks:
                          // 1. all of the nodes of the same SCC get the same priority
                          // 2. first node of the topological sorting gets the highest priority (because has least dependencies)
                          comps =>
                              comps.foreach(comp =>
                                  depCount += (comp -> {
                                      index
                                  })
                              )
                        )
                    }
                } else {}

    trait LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_With_Check2[Expr <: Expression]
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
                                index
                            })
                        )
                    }
                    //          println(s"depcount: ${depCount}")

                    //          println(depCount)
                }

    trait LiveLeastDependenciesFirstWorklistAlgorithm_CallersOnly_With_Check[Expr <: Expression]
        extends PriorityQueueWorklistAlgorithm[Expr]
        with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
        var old_graph: mutable.Map[Component, mutable.Set[Component]] = mutable.Map()

        override def intraAnalysis(component: Component): LiveDependencyTrackingIntraa

        trait LiveDependencyTrackingIntraa extends DependencyTrackingIntra:

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
                                sortedNodes.length - index
                            })
                        )
                    }
                    //          println(s"depcount: ${depCount}")

                    //          println(depCount)
                }

    trait Main_Last_Heuristic[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr]:
        var depth: Map[Component, Int] = Map.empty.withDefaultValue(0) + (initialComponent -> -100)
        lazy val ordering: Ordering[Component] = Ordering.by(depth)(Ordering.Int)
    trait LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_Without_Check[Expr <: Expression]
        extends PriorityQueueWorklistAlgorithm[Expr]
        with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)

        override def intraAnalysis(component: Component): LiveDependencyTrackingIntraaa

        trait LiveDependencyTrackingIntraaa extends DependencyTrackingIntra:

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

    trait WeirdestHeuristic[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)

    trait MostDependenciesFirstWorklistAlgorithmPOC[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
        private var callDependencies: mutable.Map[Component, mutable.Set[Component]] = mutable.Map().withDefaultValue(mutable.Set.empty)

        def updateDependencies(
            deps: mutable.Map[Component, mutable.Set[Component]],
            readDeps: Map[Component, Set[Address]],
            writeDeps: Map[Component, Set[Address]]
          ): Int =

            // adding read and write dependencies to the graph that is in DependencyTracking
            for {
                (reader, addresses) <- readDeps
                address <- addresses
                writer <- writeDeps.keys if writeDeps(writer)(address)
            } {
                addEdge(writer, reader)
            }

            // a graph to test how Tarjan.collapse works
            val test_graph = Map("a" -> Set("b"), "b" -> Set("c"), "c" -> Set("d"), "d" -> Set("a"))

            // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
            // Care must be taken in case the graph consists of only 1 strongly connected component,
            // because in that case you actually get back a graph with only 1 node.
            val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)

            if sccs.toList.length == 1 then
                // code to only work with call dependencies
                callDependencies = deps
                deps.keySet.foreach(comp => {
                    val currDep = deps.getOrElse(comp, Set.empty)
                    depCount += (comp -> currDep.size)
                })
                return sccs.toList.length
            else {

                /// Now we are going to construct a new graph that has as
                /// nodes the strongly connected components of the original graph

                // a map from the new graph nodes to the original graph nodes
                val newToOrigNodes: Map[String, Set[Component]] = sccs.zipWithIndex.map { case (nodes, idx) =>
                    val newNode = s"node$idx"
                    newNode -> nodes
                }.toMap

                // constructing the new graph
                val newGraph: Map[String, Set[String]] = sccEdges.map { case (from, tos) =>
                    val fromNode = newToOrigNodes.find(_._2 == from).map(_._1).get
                    val toNodes = tos.flatMap(t => newToOrigNodes.find(_._2 == t).map(_._1))
                    fromNode -> toNodes
                }

                // applying topological sorting
                val sortedNodes = TopSort.topsort(newGraph.keys.toList, newGraph)

                // updating the ordering of the priority queue based on the
                // number of dependencies
                sortedNodes.zipWithIndex.foreach { case (node, index) =>
                    newToOrigNodes
                        .get(node)
                        .get
                        .foreach(
                          // remarks:
                          // 1. all of the nodes of the same SCC get the same priority
                          // 2. first node of the topological sorting gets the highest priority (because has least dependencies)
                          comp =>
                              depCount += (comp -> {
                                  index
                              })
                        )
                }
                return sccs.toList.length
            }

    trait OnlyDependenciesFirstWorklistAlgorithmPOC[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
        private var callDependencies: mutable.Map[Component, mutable.Set[Component]] = mutable.Map().withDefaultValue(mutable.Set.empty)

        def updateDependencies(
            deps: mutable.Map[Component, mutable.Set[Component]],
            readDeps: Map[Component, Set[Address]],
            writeDeps: Map[Component, Set[Address]]
          ): Unit =

            // code to only work with call dependencies
            callDependencies = deps
            deps.keySet.foreach(comp => {
                val currDep = deps.getOrElse(comp, Set.empty)
                depCount += (comp -> -currDep.size)
            })

    trait OnlyDependenciesFirstWorklistAlgorithmPOC_Tarjan[Expr <: Expression]
        extends PriorityQueueWorklistAlgorithm[Expr]
        with DependencyTracking[Expr]:
        var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
        lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)

        def updateDependencies(
            deps: mutable.Map[Component, mutable.Set[Component]],
            readDeps: Map[Component, Set[Address]],
            writeDeps: Map[Component, Set[Address]]
          ): Int =
            graph = deps

            depCount = Map.empty.withDefaultValue(0)
            // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
            // Care must be taken in case the graph consists of only 1 strongly connected component,
            // because in that case you actually get back a graph with only 1 node.
            val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)

            // applying topological sorting
            val sortedNodes = TopSort.topsort(sccs.toList, sccEdges)

            println(s"LENGTH: ${sccs.toList.length}")

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
            return sccs.toList.length

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

    def randomAnalysis(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with RandomWorklistAlgorithm[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    def least_dependencies_first(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with LeastDependenciesFirstWorklistAlgorithmPOC[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    def most_dependencies_first(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with MostDependenciesFirstWorklistAlgorithmPOC[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    def call_dependencies_only(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with OnlyDependenciesFirstWorklistAlgorithmPOC[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    def call_dependencies_only_with_Tarjan(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with OnlyDependenciesFirstWorklistAlgorithmPOC_Tarjan[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    def liveAnalysis(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with GlobalStore[SchemeExp]
            with LiveLeastDependenciesFirstWorklistAlgorithm[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with LiveDependencyTrackingIntra
        }

    def liveAnalysis_CallsOnly_With_Check(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with GlobalStore[SchemeExp]
            with LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_With_Check2[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with LiveDependencyTrackingIntra
        }

    def liveAnalysis_CallersOnly_With_Check(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with GlobalStore[SchemeExp]
            with LiveLeastDependenciesFirstWorklistAlgorithm_CallersOnly_With_Check[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with LiveDependencyTrackingIntraa
        }

    def liveAnalysis_Main_Last(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with GlobalStore[SchemeExp]
            with Main_Last_Heuristic[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    def liveAnalysis_CallsOnly_Without_Check(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with GlobalStore[SchemeExp]
            with LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_Without_Check[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with LiveDependencyTrackingIntraaa
        }

    def weirdest_analysis(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with GlobalStore[SchemeExp]
            with WeirdestHeuristic[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
        }

    val bench2: Map[String, String] = List(
      ("test/R5RS/gambit/sboyer.scm", "sboyer")
    ).toMap

    val bench3: Map[String, String] = List(
      ("test/R5RS/gambit/sboyer.scm", "sboyer")
    ).toMap

    def vectorSum(vec: Vector[Long]): Long = {
        var sum: Long = 0
        for (i <- vec.indices) {
            sum = sum + vec(i)
        }
        sum
    }

    val bench: Map[String, String] = List(
      ("test/R5RS/gambit/scheme.scm", "scheme"),
      ("test/R5RS/icp/icp_7_eceval.scm", "eceval"),
      ("test/R5RS/gambit/sboyer.scm", "sboyer"),
      ("test/R5RS/gambit/peval.scm", "peval"),
      ("test/R5RS/icp/icp_1c_multiple-dwelling.scm", "multiple-dwelling"),
      ("test/R5RS/icp/icp_1c_prime-sum-pair.scm", "prime-sum-pair"),
      ("test/R5RS/WeiChenRompf2019/toplas98/boyer.scm", "boyer"),
      ("test/R5RS/various/SICP-compiler.scm", "SICP-compiler"),
      ("test/R5RS/icp/icp_8_compiler.scm", "compiler"),
    ).toMap

    val analyses = List(
      ("random", randomAnalysis),
      ("FIFO", FIFOanalysis),
      ("LIFO", LIFOanalysis),
      ("LDP", least_dependencies_first),
      ("POC", call_dependencies_only_with_Tarjan),
      ("LIVE", liveAnalysis),
      ("CAD", liveAnalysis_CallersOnly_With_Check),
      ("CED", liveAnalysis_CallersOnly_With_Check)
    )

    var outputTable: Table[Double] = Table.empty
    bench.toList
        .cartesian(analyses)
        .foreach { case ((filename, name), (analysisType, makeAnalysis)) =>
            print(s"Analyzing $filename with $analysisType ")
            val program = SchemeParser.parseProgram(Reader.loadFile(filename))

            // Run
            val results = (1 to (warmup + numIterations))
                .map(i =>
                    print(i)
                    val anl = makeAnalysis(program)
                    val (result, timeTaken) = timeAnalysis((name, program), anl, analysisType)
                    (result.map(_._2).foldLeft(0)(_ + _), timeTaken / 1000 * 1000)
                )
                .drop(warmup)

            println()
            // Compute metrics
            val stats = Statistics.all(results.map(_._2).toList)
            outputTable = outputTable.add(s"${name}_$analysisType", "time_mean", stats.mean)
            outputTable = outputTable.add(s"${name}_$analysisType", "time_stdev", stats.stddev)
            outputTable = outputTable.add(s"${name}_$analysisType", "time_median", stats.median)
            outputTable = outputTable.add(s"${name}_$analysisType", "# iterations", results.head._1)

            // Flush the output table to a file
            val outputString = outputTable.toCSVString()
            val file = Writer.openTimeStamped("output/results.csv")
            Writer.write(file, outputString)
            Writer.close(file)
        }
