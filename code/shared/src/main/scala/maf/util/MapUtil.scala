package maf.util

object MapUtil:
    extension [A, B](from: Map[A, Set[B]])
        def invert: Map[B, Set[A]] =
            from.foldLeft(Map[B, Set[A]]()) { case (map, (key, value)) =>
                value.foldLeft(map)((map, vlu) => map.updatedWith(vlu)(v => Some(v.map(_ + key).getOrElse(Set(key)))))
            }
