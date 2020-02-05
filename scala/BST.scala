import scala.language.implicitConversions

import nat_operation._

sealed trait BST 
case class Node(sx : BST, el : nat, dx : BST) extends BST
object Empty extends BST

object bst_operation {
    implicit def toString(bst : BST) : String = bst match {
        case Empty => "empty"
        case Node(sx, el, dx) => "(" + sx + el + dx + ")" 
    }
    
    def insert (El : nat) (bst : BST) : BST = bst match {
        case Empty => Node(Empty, El, Empty)
        case Node(sx, el, dx) => compare(el, El) match {
            case Eq => bst
            case Lt => Node(sx, el, insert(El)(dx))
            case Gt => Node(insert(El)(sx), el, dx)
        }
    }
    
    def fromList(l : List[nat]) : BST = l match {
        case Nil => Empty
        case h :: t => insert(h)(fromList(t))
    }
    
    def size(bst : BST) : nat = bst match {
        case Empty => 0
        case Node(sx, _, dx) => size(sx) + size(dx) + 1
    }
    
    def isEmpty(bst : BST) : Boolean = bst match {
        case Empty => true
        case _ => false
    }
    
    def toList(bst : BST) : List[nat] = bst match {
        case Empty => Nil
        case Node(sx, el, dx) => toList(sx) ++ (el :: Nil) ++ toList(dx)
    }
    
    def getMin(bst : BST) : Option[nat] = bst match {
        case Empty => None
        case Node(Empty, el, _) => Some(el)
        case Node(sx, _, _) => getMin(sx)
    }

    def getMax(bst : BST) : Option[nat] = bst match {
        case Empty => None
        case Node(_, el, Empty) => Some(el)
        case Node(_, _, dx) => getMax(dx) 
    }

    def isMember(El : nat)(bst : BST) : Boolean = bst match {
        case Empty => false
        case Node(sx, el, dx) =>
            compare(el, El) match {
              case Eq => true
              case Lt => isMember(El)(dx)
              case Gt => isMember(El)(sx)
            }
    }

    def delete(El : nat)(bst : BST) : BST = bst match {
        case Empty => bst
        case Node(sx, el, dx) =>
            compare(el, El) match {
              case Eq => 
                  getMin(dx) match {
                    case None => sx
                    case Some(min) => Node(sx, min, (delete(min)(dx)))
                  }
              case Lt => Node(sx, el, (delete(El)(dx)))
              case Gt => Node(delete(El)(sx), el, dx)
            }
    }

    def correct_fun(bst : BST) : Boolean = bst match {
        case Empty => true
        case Node(sx, e, dx) => (sx, dx) match {
              case (Empty, Empty) => true
              case (Node(ssx, esx, dsx), Empty) => 
                  compare(esx, e) match { 
                    case Lt => correct_fun(sx)
                    case _ => false
                  }
              case (Empty, Node(sdx, edx, ddx)) => 
                  compare(edx, e) match {
                    case Gt => correct_fun(dx)
                    case _ => false
                  }
              case (Node(ssx, esx, dsx), Node(sdx, edx, ddx)) => 
                  (compare(esx, e), compare(edx, e)) match {
                    case (Lt, Gt) => (correct_fun(sx)) && (correct_fun(dx))
                    case _ => false
                  }
            }
      }
}