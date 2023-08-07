package maf.test.util

import maf.util.graph.*
import maf.test.UtilityTest
import org.scalatest.propspec.AnyPropSpec
import cats.data.OpInstances0

class FloydWarshallTests extends AnyPropSpec:
    case class FloydWarshallTest[N](
        id: Int,
        nodes: Set[N],
        edges: Map[N, Set[N]],
        weights: Map[(N, N), Double],
        expected: Map[(N, N), Double]):
        def test(): Unit =
            property(s"Floywarshall correctly computes the smallest weight for the given graph $id", UtilityTest) {
                assert(FloydWarshall.floydwarshall(nodes, edges, weights, Double.PositiveInfinity) == expected)
            }

    val graphs: List[FloydWarshallTest[Int]] = List(
      // From: https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm
      FloydWarshallTest(
        0,
        nodes = Set(1, 2, 3, 4),
        edges = Map(
          1 -> Set(3),
          2 -> Set(3, 1),
          3 -> Set(4),
          4 -> Set(2)
        ),
        weights = Map(
          (1, 3) -> -2.0,
          (2, 1) -> 4.0,
          (2, 3) -> 3,
          (3, 4) -> 2,
          (4, 2) -> -1
        ),
        expected = Map(
          (1, 1) -> 0.0,
          (1, 2) -> -1.0,
          (1, 3) -> -2.0,
          (1, 4) -> 0.0,
          (2, 1) -> 4.0,
          (2, 2) -> 0.0,
          (2, 3) -> 2.0,
          (2, 4) -> 4.0,
          (3, 1) -> 5.0,
          (3, 2) -> 1.0,
          (3, 3) -> 0.0,
          (3, 4) -> 2.0,
          (4, 1) -> 3.0,
          (4, 2) -> -1.0,
          (4, 3) -> 1.0,
          (4, 4) -> 0.0
        )
      )
    )

    graphs.foreach(_.test())
