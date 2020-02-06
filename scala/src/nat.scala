package src

import scala.language.implicitConversions

sealed trait nat

case object O extends nat
case class S(n : Int) extends nat {
    require(n >= 0, "Negative natural error")
}

object nat_operation {
    implicit def toInt(n : nat) : Int = n match {
        case O => 0
        case S(p) => 1 + p
    }
    
    implicit def toString(n : nat) : String = toInt(n).toString
 
    implicit def compare(n : nat, m : nat) : comparison = 
        if (n - m < 0) Lt
        else if (n - m == 0) Eq
        else Gt
    
    implicit def toNat(i : Int) : nat = if (i <= 0) O else S(i - 1)    
}
