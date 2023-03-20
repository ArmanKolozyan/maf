package maf.cli.runnables

import maf.core.{Address, Expression}
import maf.language.scheme.{SchemeExp, SchemeParser}
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scheme.modf.{SchemeModFComponent, SchemeModFKCallSiteSensitivity, SchemeModFNoSensitivity, SimpleSchemeModFAnalysis, StandardSchemeModFComponents}
import maf.modular.{Dependency, DependencyTracking, ModAnalysis}
import maf.modular.worklist.{MostDependenciesFirstWorklistAlgorithm, PriorityQueueWorklistAlgorithm, RandomWorklistAlgorithm}
import maf.util.Reader
import maf.util.benchmarks.Timer
import maf.util.graph.{Tarjan, TopSort}
import maf.util.Wrapper.instance
import maf.util.Wrapper2.instance

import scala.collection.mutable


object DynamicWorklistAlgorithms extends App:

  trait MostDependenciesFirstWorklistAlgorithm[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] with DependencyTracking[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(depCount)
    private var callDependencies: Map[Component, Set[Component]] = Map().withDefaultValue(Set.empty)

    def updateDependencies(deps: Map[Component, Set[Component]], readDeps: Map[Component, Set[Address]], writeDeps: Map[Component, Set[Address]]): Unit =


      // code to only work with call dependencies (commented out)
      // call dependencies
      /*
      callDependencies = deps
      deps.keySet.foreach(comp => {
        val currDep = deps.getOrElse(comp, Set.empty)
        depCount += (comp -> currDep.size)
      })*/


      // adding read and write dependencies to the graph that is in DependencyTracking
      for ((reader, addresses) <- readDeps; address <- addresses; writer <- writeDeps.keys if writeDeps(writer)(address)) {
        addEdge(reader, writer)
      }

      // a graph to test how Tarjan.collapse works
      val test_graph = Map("a" -> Set("b"), "b" -> Set("c"), "c" -> Set("d"), "d" -> Set("a"))

      // applying Tarjan.collapse to (ideally) get a DAG (Directed Acyclic Graph)
      // Care must be taken in case the graph consists of only 1 strongly connected component,
      // because in that case you actually get back a graph with only 1 node.
      val (sccs, sccEdges) = Tarjan.collapse(graph.keys.toSet, graph.map { case (k, v) => (k, v.toSet) }.toMap)


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




  type Deps = Map[SchemeModFComponent, Set[SchemeModFComponent]]
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

  def depAnalysis(program: SchemeExp) =
    new SimpleSchemeModFAnalysis(program)
      with SchemeModFNoSensitivity
      with SchemeConstantPropagationDomain
      with DependencyTracking[SchemeExp]
      with MostDependenciesFirstWorklistAlgorithm[SchemeExp] {
      override def intraAnalysis(cmp: SchemeModFComponent) =
        new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
    }

  val bench: Map[String, String] = List(
    ("test/R5RS/ad/all.scm", "ad"),
  ).toMap

  bench.foreach({ b =>
        val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once
        val analysis = depAnalysis(program)
        val dependencies = runAnalysis((b._2, program), program => randomAnalysis(program))
        analysis.updateDependencies(dependencies._1, dependencies._2, dependencies._3)
        analysis.analyze()})
