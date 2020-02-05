package src

sealed trait comparison
case object Eq extends comparison
case object Lt extends comparison
case object Gt extends comparison
