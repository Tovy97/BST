import scala.language.implicitConversions

sealed trait nat
object O extends nat
case class S(n : nat) extends nat

object nat_operation {
    implicit def toInt(n : nat) : Int = n match {
        case O => 0
        case S(p) => 1 + toInt(p)
    }
    implicit def toString(n : nat) : String = toInt(n).toString
    implicit def compare(n : nat, m : nat) : comparison = (n, m) match {
        case (O, O) => Eq
        case (O, S(_)) => Lt
        case (S(_), O) => Gt
        case (S(n1), S(m1)) => compare(n1, m1)        
    }
    implicit def toNat(i : Int) : nat = if (i <= 0) O else S(i - 1)
}
