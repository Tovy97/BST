package test

import org.scalacheck.Prop.forAll
import org.scalacheck.{Arbitrary, Gen, Properties}
import src._
import src.bst_operation._
import src.nat_operation._

object BST_Specification extends Properties("BST") {
    
    private val genNat : Gen[nat] = for {
        n <- Arbitrary.arbitrary[Int]
    } yield n
    
    private val genTree: Gen[BST] = for {
        list <- Gen.listOf[nat](genNat)
    } yield fromList(list)
    
    property("correct_gen1") = forAll(genNat) { n : nat =>
        n >= O
    }
    
    property("correct_gen2") = forAll(genTree) { bst : BST =>
        size(bst) >= O
    }
    
    property("correct_gen3") = forAll(genTree) { bst : BST =>
        correct_fun(bst)
    }
    
    property("max_height") = forAll(genTree) { bst : BST => 
        if (correct_fun(bst))            
            (compare(height(bst), size(bst)) == Lt || compare(height(bst), size(bst)) == Eq)
        else true
    }
  
    property("child_correct") = forAll(genTree, genTree, genNat) { (l : BST, r : BST, el : nat) =>
        if (correct_fun(Node(l, el, r)))
            correct_fun(l) && correct_fun(r)
        else true
    }
    
    property("insert_correct_on_r") = forAll(genNat, genNat, genTree) { (e : nat, a : nat, bst : BST) =>
        if (e < a)
            if (correct_on_r(e)(bst) == true)
                correct_on_r(e)(insert(a)(bst)) == true
            else true
        else true
    }
    
    property("insert_correct_on_l") = forAll(genNat, genNat, genTree) { (e : nat, a : nat, bst : BST) =>
        if (a < e)
            if (correct_on_l(e)(bst) == true)
                correct_on_l(e)(insert(a)(bst)) == true
            else true
        else true
    }

    property("insert_correct") = forAll(genTree, genNat) { (bst : BST, a : nat) =>
        if (correct_fun(bst))
            correct_fun(insert(a)(bst))
        else true
    }
    
    property("fromList_correct") = forAll(Gen.listOf[nat](genNat)) { l: List[nat] =>
        correct_fun(fromList(l))
    }
    
    property("insert_ismember") = forAll(genTree, genNat) { (bst : BST, el : nat) =>
        if (correct_fun(bst))
            isMember(el)(insert(el)(bst))
        else true
    }
    
    property("insert_size") = forAll(genTree, genNat) { (bst : BST, el : nat) =>
        if (correct_fun(bst)) {
            (
                if (isMember(el)(bst) == true) 
                    size(insert(el)(bst)) == size(bst)
                else true
            ) && (
                if (isMember(el)(bst) == false) 
                    size(insert(el)(bst)) == toNat(size(bst) + 1)
                else true
            )
        } else true
    }
    
    property("toList_size") = forAll(genTree) { bst : BST =>
         if (correct_fun(bst))
            toNat(toList(bst).size) == size(bst)
         else true
    }
    
    property("size_isEmpty") = forAll(genTree) { bst : BST =>
        if (correct_fun(bst)) {
            (
                if(isEmpty(bst) == true)
                    size(bst) == O
                else true
            ) && (
                if(size(bst) == O)
                    isEmpty(bst) == true
                else true
            )
         } else true
    }
    
    property("delete_equals_delete2") = forAll(genTree, genNat) { (bst : BST, el : nat) =>
        if (correct_fun(bst))
            BSTequals(delete(el)(bst))(delete2(el)(bst)) == true
        else true
    }
    
    property("insert_ismember2") = forAll(genTree, genNat, genNat) { (bst : BST, a : nat, b : nat) =>
        if (correct_fun(bst)) {
            if (isMember(a)(bst) == false) {
                if (b != a)
                    isMember(a)(insert(b)(bst)) == false
                else true
            } else true
        } else true
    }
    
    property("delete2_l") = forAll(genTree, genTree, genNat, genNat) { (l : BST, r : BST, a : nat, el : nat) =>
        if (correct_fun(Node(l, el, r))) {
            if (compare(el, a) == Gt) {
                delete2(a)(Node(l, el, r)) == Node(delete2(a)(l), el, r)
            } else true
        } else true
    }

    property("delete2_r") = forAll(genTree, genTree, genNat, genNat) { (l : BST, r : BST, a : nat, el : nat) =>
        if (correct_fun(Node(l, el, r))) {
            if (compare(el, a) == Lt) {
                delete2(a)(Node(l, el, r)) == Node(l, el, delete2(a)(r))
            } else true
        } else true
    }
    
    property("delete_correct") = forAll(genTree, genNat) { (bst : BST, a : nat) =>
        if (correct_fun(bst))
            correct_fun(delete(a)(bst))
        else true
    }
    
    property("delete_ismember") = forAll(genTree, genNat) { (bst : BST, el : nat) =>
        if (correct_fun(bst))
            isMember(el)(delete(el)(bst)) == false
        else true
    }

    property("delete_size") = forAll(genTree, genNat) { (bst : BST, el : nat) =>
        if (correct_fun(bst)) {
            (
                if(isMember(el)(bst) == true)
                    size(delete(el)(bst)) == toNat(size(bst) - 1)
                else true
            ) && ( 
                if(isMember(el)(bst) == false) 
                    size(delete(el)(bst)) == size(bst)
                else true
            )
        } else true
    }

    private def not_in(l : List[nat])(n : nat): Boolean = l match {
        case Nil => true
        case h :: t =>
            compare(h, n) match {
                case Eq => false
                case _ => not_in(t)(n)
            }
    }

    private def only_one (l : List[nat])(n : nat) : Boolean = l match {
        case Nil => false
        case h :: t => 
            compare(h, n) match {
              case Eq => not_in(t)(n)
              case _ => only_one(t)(n)
            }
    }

    property("toList_distinct") = forAll(genTree, genNat) { (bst : BST, n : nat) =>
        if (correct_fun(bst)) {
            (
                if(isMember(n)(bst) == true)
                    only_one(toList(bst))(n) == true
                else true
            ) && (
                if(isMember(n)(bst) == false) 
                    not_in(toList(bst))(n) == true
                else true
            )
        }   
        else true
    }

    private def sorted (l : List[nat]) : Boolean = l match {
        case Nil => true
        case h1 :: t => 
            t match {
              case Nil => true
              case h2 :: _ =>
                  compare(h1, h2) match {
                    case Lt => sorted(t)
                    case _ => false
                  }
            }
     }
     
     property("toList_sorted") = forAll(genTree) { bst : BST =>
         if (correct_fun(bst))
            sorted(toList(bst)) == true
         else true
     }

    property("list_head_last") = forAll(genTree) { bst : BST =>
         if (correct_fun(bst)) {
            ((toList(bst)).headOption == getMin(bst)) && 
            ((toList(bst)).reverse.headOption == getMax(bst))
         } else true
     }
}
