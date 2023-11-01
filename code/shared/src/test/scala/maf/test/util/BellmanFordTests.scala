package maf.test.util

import maf.util.graph.*
import maf.test.UtilityTest
import org.scalatest.propspec.AnyPropSpec
import cats.data.OpInstances0

class BellmanFordTests extends AnyPropSpec:
    case class BellmanFordTest[N](
                                       id: Int,
                                       nodes: Set[N],
                                       edges: Map[N, Set[N]],
                                       weights: Map[(N, N), Double],
                                       expected: Boolean):
        def test(): Unit =
            property(s"Bellman-Ford correctly checks for a negative cycle in the given graph with id $id", UtilityTest) {
                assert(BellmanFord.hasNegativeCycle(nodes, edges, weights, Double.PositiveInfinity) == expected)
            }


    val graphs: List[BellmanFordTest[String]] = List(
        BellmanFordTest(
          0,
            nodes = Set("A", "B", "C"),
            edges = Map(
                "A" -> Set("B"),
                "B" -> Set("C"),
                "C" -> Set("A"),
            ),
            weights = Map(
                ("A", "B") -> 1.0,
                ("B", "C") -> -3.0,
                ("C", "A") -> 1.0
            ),
            expected = true
        ),
        BellmanFordTest(
            1,
            nodes = Set("A", "B", "C"),
            edges = Map(
                "A" -> Set("B"),
                "B" -> Set("C"),
                "C" -> Set("A"),
            ),
            weights = Map(
                ("A", "B") -> 1.0,
                ("B", "C") -> -1.0,
                ("C", "A") -> 1.0
            ),
            expected = false
        )
    )

    graphs.foreach(_.test())
