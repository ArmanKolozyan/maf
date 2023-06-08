package maf.cli.runnables

import maf.cli.runnables.AnalyzeWorklistAlgorithms.{FIFOanalysis, LIFOanalysis, numIterations, timeAnalysis, warmup}
import maf.cli.runnables.DynamicWorklistAlgorithms.{LeastDependenciesFirstWorklistAlgorithmPOC, LiveLeastDependenciesFirstWorklistAlgorithm, LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_With_Check2}
import maf.core.{Address, Expression}
import maf.language.scheme.{SchemeExp, SchemeParser}
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scheme.modf.{SchemeModFComponent, SchemeModFKCallSiteSensitivity, SchemeModFNoSensitivity, SimpleSchemeModFAnalysis, StandardSchemeModFComponents}
import maf.modular.{Dependency, DependencyTracking, GlobalStore, ModAnalysis}
import maf.modular.worklist.{LeastDependenciesFirstWorklistAlgorithm, PriorityQueueWorklistAlgorithm, RandomWorklistAlgorithm, SequentialWorklistAlgorithm}
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


object DynamicWorklistAlgorithms extends App:

  trait LeastDependenciesFirstWorklistAlgorithmPOC[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
    private var callDependencies: mutable.Map[Component, mutable.Set[Component]] = mutable.Map().withDefaultValue(mutable.Set.empty)

    def updateDependencies(deps: mutable.Map[Component, mutable.Set[Component]], readDeps: Map[Component, Set[Address]], writeDeps: Map[Component, Set[Address]]): Int =


      // adding read and write dependencies to the graph that is in DependencyTracking
      for ((reader, addresses) <- readDeps; address <- addresses; writer <- writeDeps.keys if writeDeps(writer)(address)) {
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
          depCount += (comp -> - currDep.size)
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
          newToOrigNodes.get(node).get.foreach(
            // remarks:
            // 1. all of the nodes of the same SCC get the same priority
            // 2. first node of the topological sorting gets the highest priority (because has least dependencies)
            comp => depCount += (comp -> {
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
        for ((reader, addresses) <- readDependencies; address <- addresses; writer <- writeEffects.keys if writeEffects(writer)(address)) {
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
            newToOrigNodes.get(node).get.foreach(
              // remarks:
              // 1. all of the nodes of the same SCC get the same priority
              // 2. first node of the topological sorting gets the highest priority (because has least dependencies)
              comp => depCount += (comp -> {
                sortedNodes.length - index
              })
            )
          }
        }


  def mySum[T](list: List[T])(implicit num: Numeric[T]): T = {
    list.foldLeft(num.zero)(num.plus)
  }

  trait LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_With_Check[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
    var old_graph: mutable.Map[Component, mutable.Set[Component]] = mutable.Map()

    override def intraAnalysis(component: Component): LiveDependencyTrackingIntra

    trait LiveDependencyTrackingIntra extends DependencyTrackingIntra :

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
              comps => comps.foreach(
                comp => depCount += (comp -> {
                  index
                }
                  )
              )
            )
          }
        }
        else {
        }

  trait LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_With_Check2[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
    var old_graph: mutable.Map[Component, mutable.Set[Component]] = mutable.Map()

    override def intraAnalysis(component: Component): LiveDependencyTrackingIntra

    trait LiveDependencyTrackingIntra extends DependencyTrackingIntra :

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
            comps.foreach(
              comp => depCount += (comp -> {
                index
              }
                )
            )
          }
          //          println(s"depcount: ${depCount}")


          //          println(depCount)
        }

  trait LiveLeastDependenciesFirstWorklistAlgorithm_CallersOnly_With_Check[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
    var old_graph: mutable.Map[Component, mutable.Set[Component]] = mutable.Map()

    override def intraAnalysis(component: Component): LiveDependencyTrackingIntraa

    trait LiveDependencyTrackingIntraa extends DependencyTrackingIntra :

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
            comps.foreach(
              comp => depCount += (comp -> {
                sortedNodes.length - index
              }
                )
            )
          }
          //          println(s"depcount: ${depCount}")


          //          println(depCount)
        }


  trait Main_Last_Heuristic[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] :
    var depth: Map[Component, Int] = Map.empty.withDefaultValue(0) + (initialComponent -> -100)
    lazy val ordering: Ordering[Component] = Ordering.by(depth)(Ordering.Int)
  trait LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_Without_Check[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)

    override def intraAnalysis(component: Component): LiveDependencyTrackingIntraaa

    trait LiveDependencyTrackingIntraaa extends DependencyTrackingIntra :

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
          comps.foreach(
            comp => depCount += (comp -> {
              index
            }
              )
          )
        }

  trait WeirdestHeuristic[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)


  trait MostDependenciesFirstWorklistAlgorithmPOC[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
    private var callDependencies: mutable.Map[Component, mutable.Set[Component]] = mutable.Map().withDefaultValue(mutable.Set.empty)

    def updateDependencies(deps: mutable.Map[Component, mutable.Set[Component]], readDeps: Map[Component, Set[Address]], writeDeps: Map[Component, Set[Address]]): Int =


      // adding read and write dependencies to the graph that is in DependencyTracking
      for ((reader, addresses) <- readDeps; address <- addresses; writer <- writeDeps.keys if writeDeps(writer)(address)) {
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
          newToOrigNodes.get(node).get.foreach(
            // remarks:
            // 1. all of the nodes of the same SCC get the same priority
            // 2. first node of the topological sorting gets the highest priority (because has least dependencies)
            comp => depCount += (comp -> {
              index
            })
          )
        }
        return sccs.toList.length
      }

  trait OnlyDependenciesFirstWorklistAlgorithmPOC[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)
    private var callDependencies: mutable.Map[Component, mutable.Set[Component]] = mutable.Map().withDefaultValue(mutable.Set.empty)

    def updateDependencies(deps: mutable.Map[Component, mutable.Set[Component]], readDeps: Map[Component, Set[Address]], writeDeps: Map[Component, Set[Address]]): Unit =

      // code to only work with call dependencies
      callDependencies = deps
      deps.keySet.foreach(comp => {
        val currDep = deps.getOrElse(comp, Set.empty)
        depCount += (comp -> -currDep.size)
      })


  trait OnlyDependenciesFirstWorklistAlgorithmPOC_Tarjan[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(cmp => depCount(cmp))(Ordering.Int)

    def updateDependencies(deps: mutable.Map[Component, mutable.Set[Component]], readDeps: Map[Component, Set[Address]], writeDeps: Map[Component, Set[Address]]): Int =
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
        comps.foreach(
          comp => depCount += (comp -> {
            index
          }
            )
        )
      }
      return sccs.toList.length




  type Deps = mutable.Map[SchemeModFComponent, mutable.Set[SchemeModFComponent]]
  type GraphDeps = Map[SchemeModFComponent, Set[Address]]
  type SchemeAnalysisWithDeps = ModAnalysis[SchemeExp] with DependencyTracking[SchemeExp] with StandardSchemeModFComponents

  def runAnalysis[A <: SchemeAnalysisWithDeps] (bench: (String, SchemeExp), analysis: SchemeExp => A): (Deps, GraphDeps, GraphDeps) =
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

  /*bench.foreach({ b =>
    val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once
    val dependencies = runAnalysis((b._2, program), program => randomAnalysis(program))
    val results: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
          val a = least_dependencies_first(program)
          a.updateDependencies(dependencies._1, dependencies._2, dependencies._3)
          val result = timeAnalysis((b._2, program), a, "POC_least")
          result._2
        )
    val statistics1 = Statistics.all(results.drop(warmup).toList)
    // val avgTime = vectorSum(results.drop(warmup).toVector) / numIterations.toDouble
    println(s"Statistics for POC_least on ${b._2}: ${statistics1}")
    println()
    println()
    val results2: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val a = randomAnalysis(program)
      val result = timeAnalysis((b._2, program), a, "Random")
        result._2
    )
    val statistics2 = Statistics.all(results2.drop(warmup).toList)
    println(s"Statistics for Random on ${b._2}: ${statistics2}")
    println()
    println()
    val results3: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val a = most_dependencies_first(program)
        a
      .updateDependencies(dependencies._1, dependencies._2, dependencies._3)
      val result = timeAnalysis((b._2, program), a, "POC_most")
        result
      ._2
    )
    val statistics3 = Statistics.all(results3.drop(warmup).toList)
    println(s"Statistics for POC_most on ${b._2}: ${statistics3}")

    val least_first = least_dependencies_first(program)
    val SCCs_least: Int = least_first.updateDependencies(dependencies._1, dependencies._2, dependencies._3)
    println()
    println()
    println(s"Number of SCCs of least_dependencies_first on ${b._2}: ${SCCs_least} ")
    println()

/*    val results4: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val a = call_dependencies_only(program)
        a.updateDependencies(dependencies._1, dependencies._2, dependencies._3)
      val result = timeAnalysis((b._2, program), a, "POC_only_call")
        result._2
    )
    val statistics4 = Statistics.all(results4.drop(warmup).toList)
    println(s"Statistics time for POC_only_call on ${b._2}: ${statistics4}")
    println()
    println()*/
    val results4: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
          val a = call_dependencies_only_with_Tarjan(program)
          val SCCs = a.updateDependencies(dependencies._1, dependencies._2, dependencies._3)
          println(s"Number of SCCs of call_dependencies_only_with_Tarjan on ${b._2}: ${SCCs} ")
          val result = timeAnalysis((b._2, program), a, "POC_only_call_with_Tarjan")
          result._2
        )
    val statistics4 = Statistics.all(results4.drop(warmup).toList)
    println(s"Statistics time for POC_only_call_with_Tarjan on ${b._2}: ${statistics4}")
    println()
    println()
/*    val results5: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val a = liveAnalysis(program)
      val result = timeAnalysis((b._2, program), a, "Live_least_dependencies")
        result._2
    )
    val statistics5 = Statistics.all(results5.drop(warmup).toList)
    //val avgTime4 = vectorSum(results4.drop(warmup).toVector) / numIterations.toDouble
    println(s"Statistics time for Live_least_dependencies on ${b._2}: ${statistics5}")
    println()
    println()*/
    val results5: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
          val a = liveAnalysis_CallsOnly(program)
          val result = timeAnalysis((b._2, program), a, "Live_least_dependencies_CallsOnly")
            result._2
        )
    val statistics5 = Statistics.all(results5.drop(warmup).toList)
    //val avgTime4 = vectorSum(results4.drop(warmup).toVector) / numIterations.toDouble
    println(s"Statistics time for Live_least_dependencies_CallsOnly on ${b._2}: ${statistics5}")
    println()
    println()
  })*/
  //11684

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

  bench.foreach({ b =>
    println(b._2)
    val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once


    val result3: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val aaa = randomAnalysis(program)
      val result = timeAnalysis((b._2, program), aaa, "Random")
        result._2
    )
    val statistics3 = Statistics.all(result3.drop(warmup).toList)
    //val avgTime4 = vectorSum(results4.drop(warmup).toVector) / numIterations.toDouble
    println(s"Statistics time for Random on ${b._2}: ${statistics3}")


    println("----")

    val result2: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val aa = FIFOanalysis(program)
      val result = timeAnalysis((b._2, program), aa, "FIFO")
        result._2
    )
    val statistics2 = Statistics.all(result2.drop(warmup).toList)
    println(s"Statistics time for FIFO: $statistics2")

    println("----")


    val result4: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val aaaa = LIFOanalysis(program)
      val result = timeAnalysis((b._2, program), aaaa, "LIFO")
        result._2
    )
    val statistics4 = Statistics.all(result4.drop(warmup).toList)
    println(s"Statistics time for LIFO: $statistics4")

    println("----")


    var total_iterations8: Int = 0
    val dependencies = runAnalysis((b._2, program), program => randomAnalysis(program))
    val result8: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val a = least_dependencies_first(program)
        a.updateDependencies(dependencies._1, dependencies._2, dependencies._3)
      val result = timeAnalysis((b._2, program), a, "POC all dependencies")
        result._2
    )
    val statistics8 = Statistics.all(result8.drop(warmup).toList)

    println(s"Statistics time for POC all dependencies: $statistics8")

    println("----")

    val dependencies2 = runAnalysis((b._2, program), program => randomAnalysis(program))
    val result9: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val au = call_dependencies_only_with_Tarjan(program)
        au.updateDependencies(dependencies2._1, dependencies2._2, dependencies2._3)
      val result = timeAnalysis((b._2, program), au, "POC call dependencies only")
        result._2
    )
    val statistics9 = Statistics.all(result9.drop(warmup).toList)

    println(s"Statistics time for POC call dependencies only: $statistics9")

    println("----")


    val result7: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val aaaaaaa = liveAnalysis(program)
      val result = timeAnalysis((b._2, program), aaaaaaa, "Live analysis all dependencies")
        result._2
    )
    val statistics7 = Statistics.all(result7.drop(warmup).toList)
    println(s"Statistics time for Live analysis all dependencies: $statistics7")

    println("----")


    val result: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val a = liveAnalysis_CallsOnly_With_Check(program)
      val result = timeAnalysis((b._2, program), a, "Live analysis call dependencies with check")
        result._2
    )
    val statistics = Statistics.all(result.drop(warmup).toList)
    println(s"Statistics time for Live analysis call dependencies with check: $statistics")

    println("----")


    val result5 = (1 to (warmup + numIterations)).map(_ =>
      val aaaaa = liveAnalysis_CallsOnly_Without_Check(program)
      val result = timeAnalysis((b._2, program), aaaaa, "Live analysis call dependencies without check")
        result._2
    )
    val statistics5 = Statistics.all(result5.drop(warmup).toList)
    println(s"Statistics time for Live analysis call dependencies without check: $statistics5")

    println("----")


    val result6 = (1 to (warmup + numIterations)).map(_ =>
      val aaaaaa = liveAnalysis_CallersOnly_With_Check(program)
      val result = timeAnalysis((b._2, program), aaaaaa, "Live analysis caller first dependencies without check")
        result._2
    )
    val statistics6 = Statistics.all(result6.drop(warmup).toList)
    println(s"Statistics time for Live analysis caller first dependencies without check: $statistics6")

    println("----")

  })

  bench.foreach({ b =>
    println(b._2)
    val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once


    val aaa = randomAnalysis(program)
    val result3 = timeAnalysis((b._2, program), aaa, "MINE")
    var total_iterations3: Int = 0
    result3._1.foreach { case (key, value) =>
      total_iterations3 += value
    }
    println(s"Total iterations for Random: $total_iterations3")

    println("----")

    val aa = FIFOanalysis(program)
    val result2 = timeAnalysis((b._2, program), aa, "FIFO")
    var total_iterations2 = 0
    result2._1.foreach { case (key, value) =>
      total_iterations2 += value
    }
    println(s"Total iterations for FIFO: $total_iterations2")

    println("----")


    val aaaa = LIFOanalysis(program)
    val result4 = timeAnalysis((b._2, program), aaaa, "MINE")
    var total_iterations4: Int = 0
    result4._1.foreach { case (key, value) =>
      total_iterations4 += value
    }
    println(s"Total iterations for LIFO: $total_iterations4")

    println("----")


    var total_iterations8: Int = 0
    val dependencies = runAnalysis((b._2, program), program => randomAnalysis(program))
    val result8 =
      val a = least_dependencies_first(program)
      a.updateDependencies(dependencies._1, dependencies._2, dependencies._3)
      val result = timeAnalysis((b._2, program), a, "POC_least")
      result
    result8._1.foreach { case (key, value) =>
      total_iterations8 += value
    }
    println(s"Total iterations for POC all dependencies: $total_iterations8")

    println("----")

    var total_iterations9: Int = 0
    val dependencies2 = runAnalysis((b._2, program), program => randomAnalysis(program))
    val result9 =
      val a = call_dependencies_only_with_Tarjan(program)
      a.updateDependencies(dependencies2._1, dependencies2._2, dependencies2._3)
      val result = timeAnalysis((b._2, program), a, "POC_least")
      result
    result9._1.foreach { case (key, value) =>
      total_iterations9 += value
    }
    println(s"Total iterations for POC call dependencies only: $total_iterations9")

    println("----")


    val aaaaaaa = liveAnalysis(program)
    val result7 = timeAnalysis((b._2, program), aaaaaaa, "MINE")
    var total_iterations7: Int = 0
    result7._1.foreach { case (key, value) =>
      total_iterations7 += value
    }
    println(s"Total iterations for Live analysis all dependencies: $total_iterations7")

    println("----")


    val a = liveAnalysis_CallsOnly_With_Check(program)
    val result = timeAnalysis((b._2, program), a, "MINE")
    var total_iterations: Int = 0
    result._1.foreach { case (key, value) =>
      total_iterations += value
    }
    println(s"Total iterations for Live analysis call dependencies with check: $total_iterations")

    println("----")


    val aaaaa = liveAnalysis_CallsOnly_Without_Check(program)
    val result5 = timeAnalysis((b._2, program), aaaaa, "MINE")
    var total_iterations5: Int = 0
    result5._1.foreach { case (key, value) =>
      total_iterations5 += value
    }
    println(s"Total iterations for Live analysis call dependencies without check: $total_iterations5")

    println("----")


    val aaaaaa = liveAnalysis_CallersOnly_With_Check(program)
    val result6 = timeAnalysis((b._2, program), aaaaaa, "MINE")
    var total_iterations6: Int = 0
    result6._1.foreach { case (key, value) =>
      total_iterations6 += value
    }
    println(s"Total iterations for Live analysis caller first dependencies without check: $total_iterations6")

    println("----")

  })

  /*bench.foreach({ b =>
    println(b._2)
    val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once


    var total_iterations8: Int = 0
    val dependencies = runAnalysis((b._2, program), program => randomAnalysis(program))
    val adsds = randomAnalysis(program)
    adsds.analyze()
    println(s"COMPONENTS: ${adsds.analysis_stats_map.keys.toList.length}")
    val result8 =
      val a = least_dependencies_first(program)
      a.updateDependencies(dependencies._1, dependencies._2, dependencies._3)
      val result = timeAnalysis((b._2, program), a, "POC_least")
      result
    result8._1.foreach { case (key, value) =>
      total_iterations8 += value
    }
    println(s"Total iterations for POC all dependencies: $total_iterations8")

    println("----")

    var total_iterations9: Int = 0
    val dependencies2 = runAnalysis((b._2, program), program => randomAnalysis(program))
    val result9 =
      val a = call_dependencies_only_with_Tarjan(program)
      a.updateDependencies(dependencies2._1, dependencies2._2, dependencies2._3)
      val result = timeAnalysis((b._2, program), a, "POC_least")
      result
    result9._1.foreach { case (key, value) =>
      total_iterations9 += value
    }
    println(s"Total iterations for POC call dependencies only: $total_iterations9")

    println("----")

  })*/


// !!!
/*  bench.foreach({ b =>
    val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once
    var a = liveAnalysis_CallsOnly_With_Check(program)
    var result = timeAnalysis((b._2, program), a, "MINE")
    var total_iterations: Int = 0
    result._1.foreach { case (key, value) =>
     // println(s"Component: $key, Analyses: $value")
      total_iterations += value
    }
    println(b._1)
    println("A:")
    println(s"Total iterations: $total_iterations")

    println("----")


    var aa = FIFOanalysis(program)
    var result2 = timeAnalysis((b._2, program), aa, "FIFO")
    var total_iterations2 = 0
    result2._1.foreach { case (key, value) =>
   //   println(s"Component: $key, Analyses: $value")
      total_iterations2 += value
    }
    println(s"Total iterations: $total_iterations2")

    val percentage_difference = abs(total_iterations2 - total_iterations) / total_iterations * 100

      println("YEEE")
      println(b._1)
      val sortedMap = mutable.ListMap(result._1.toSeq.sortWith(_._2 < _._2): _*)
      val topThree = sortedMap.take(5)

      println("Top 5 Keys:")
      topThree.foreach { case (key, value) =>
        println(s"MINE => Key: $key, Value: $value")
        println(s"FIFO => Key: $key, Value: ${result2._1.get(key).get}")
      }
  })*/


/*  bench.foreach({ b =>
    val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once
    val results5: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val a = AnalyzeWorklistAlgorithms.mostDependenciesFirstAnalysis(program)
      val result = timeAnalysis((b._2, program), a, "mostDependenciesFirstAnalysis")
        result
      ._2
    )
    val statistics5 = Statistics.all(results5.drop(warmup).toList)
    //val avgTime4 = vectorSum(results4.drop(warmup).toVector) / numIterations.toDouble
    println(s"Statistics time for mostDependenciesFirstAnalysis on ${b._2}: ${statistics5}")
    println()
  })*/
/*
  bench.foreach({ b =>
    val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once
    val results5: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
      val a = liveAnalysis_Main_Last(program)
      val result = timeAnalysis((b._2, program), a, "Main_Last_Heuristic")
        result
      ._2
    )
    val statistics5 = Statistics.all(results5.drop(warmup).toList)
    //val avgTime4 = vectorSum(results4.drop(warmup).toVector) / numIterations.toDouble
    println(s"Statistics time for Main_Last_Heuristic on ${b._2}: ${statistics5}")
    println()
  })*/

/*
  bench3.foreach({ b =>
  val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once
  val dependencies = runAnalysis((b._2, program), program => randomAnalysis(program))
  val results2: IndexedSeq[Double] = (1 to (warmup + numIterations)).map(_ =>
    val a = randomAnalysis(program)
    val result = timeAnalysis((b._2, program), a, "Random")
    result._2
  )
  val statistics2 = Statistics.all(results2.drop(warmup).toList)
  //val avgTime2 = vectorSum(results2.drop(warmup).toVector) / numIterations.toDouble
  println(s"Statistics for Random on ${b._2}: ${statistics2}")
  println()
  println()
  })*/
