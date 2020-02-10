package src

import scala.language.implicitConversions
import src.nat_operation._
import scala.math.max

sealed trait BST 
case class Node(l : BST, el : nat, r : BST) extends BST
case object Empty extends BST

object bst_operation {
    implicit def toString(bst : BST) : String = bst match {
        case Empty => "empty"
        case Node(l, el, r) => "(" + l + el + r + ")" 
    }
    
    def insert (El : nat) (bst : BST) : BST = bst match {
        case Empty => Node(Empty, El, Empty)
        case Node(l, el, r) => compare(el, El) match {
            case Eq => bst
            case Lt => Node(l, el, insert(El)(r))
            case Gt => Node(insert(El)(l), el, r)
        }
    }
    
    def fromList(l : List[nat]) : BST = l match {
        case Nil => Empty
        case h :: t => insert(h)(fromList(t))
    }
    
    def height(bst:BST) : nat = bst match {
        case Empty => 0
        case Node(l, _, r) => max(height(l), height(r)) + 1
    }
    
    def size(bst : BST) : nat = bst match {
        case Empty => 0
        case Node(l, _, r) => size(l) + size(r) + 1
    }
    
    def isEmpty(bst : BST) : Boolean = bst match {
        case Empty => true
        case _ => false
    }
    
    def toList(bst : BST) : List[nat] = bst match {
        case Empty => Nil
        case Node(l, el, r) => toList(l) ++ (el :: Nil) ++ toList(r)
    }
    
    def getMin(bst : BST) : Option[nat] = bst match {
        case Empty => None
        case Node(Empty, el, _) => Some(el)
        case Node(l, _, _) => getMin(l)
    }

    def getMax(bst : BST) : Option[nat] = bst match {
        case Empty => None
        case Node(_, el, Empty) => Some(el)
        case Node(_, _, r) => getMax(r) 
    }

    def isMember(El : nat)(bst : BST) : Boolean = bst match {
        case Empty => false
        case Node(l, el, r) =>
            compare(el, El) match {
              case Eq => true
              case Lt => isMember(El)(r)
              case Gt => isMember(El)(l)
            }
    }

    def delete2(El : nat)(bst : BST) : BST = bst match {
        case Empty => bst
        case Node(l, el, r) =>
            compare(el, El) match {
              case Eq => 
                  getMin(r) match {
                    case None => l
                    case Some(min) => Node(l, min, (delete2(min)(r)))
                  }
              case Lt => Node(l, el, (delete2(El)(r)))
              case Gt => Node(delete2(El)(l), el, r)
            }
    }
    
    def delete(El : nat)(bst : BST) : BST =
        fromList(toList(bst).filter(El != _))

    private def list_beq(l1 : List[nat]) (l2 : List[nat]) : Boolean = (l1, l2) match {
        case (Nil, Nil) => true
        case (_ :: _, Nil) => false
        case (Nil, _ :: _) => false
        case (h1 :: t1, h2 :: t2) => 
            h1 == h2 match {
              case true => list_beq(t1)(t2)
              case false => false
            }
    }

    def BSTequals(bst1 : BST)(bst2 : BST) : Boolean = list_beq(toList(bst1))(toList(bst2))
  
    def correct_on_l(root : nat)(l : BST) : Boolean =
        (toList(l)).forall(_ < root)
    
    def correct_on_r(root : nat)(r : BST) : Boolean =
        (toList(r)).forall(root < _)

    def correct_fun(bst : BST) : Boolean = bst match {
        case Empty => true
        case Node(l, e, r) =>
            correct_on_l(e)(l) && correct_fun(l) && correct_on_r(e)(r) && correct_fun(r)
    }
}
