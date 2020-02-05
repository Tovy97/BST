package test

import org.scalacheck.Prop.forAll
import org.scalacheck.Test.{Parameters, Result, checkProperties}
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
    
    property("correct_gen") = forAll(genTree) { bst : BST =>
        correct_fun(bst)
    }
  
    property("child_correct") = forAll(genTree, genTree, genNat) { (sx : BST, dx : BST, el : nat) =>
        if (correct_fun(Node(sx, el, dx)))
            correct_fun(sx) && correct_fun(dx)
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
                    size(insert(el)(bst)) == size(bst) + 1
                else true
            )
        } else true
    }
    
    property("toList_size") = forAll(genTree) { bst : BST =>
         if (correct_fun(bst))
            toList(bst).size == size(bst)
         else true
    }
    
    property("size_isEmpty") = forAll(genTree) { bst : BST =>
        if (correct_fun(bst)) {
            (
                if(isEmpty(bst) == true)
                    size(bst) == 0
                else true
            ) && (
                if(size(bst) == 0)
                    isEmpty(bst) == true
                else true
            )
         } else true
    }
    
    property("delete_sx") = forAll(genTree, genTree, genNat, genNat) { (sx : BST, dx : BST, a : nat, el : nat) =>
        if (correct_fun(Node(sx, el, dx))) {
            if (compare(el, a) == Gt) {
                delete(a)(Node(sx, el, dx)) == Node(delete(a)(sx), el, dx)
            } else true
        } else true
    }
    
    property("delete_dx") = forAll(genTree, genTree, genNat, genNat) { (sx : BST, dx : BST, a : nat, el : nat) =>
        if (correct_fun(Node(sx, el, dx))) {
            if (compare(el, a) == Lt) {
                delete(a)(Node(sx, el, dx)) == Node(sx, el, delete(a)(dx))
            } else true
        } else true
    }

//Theorem delete_correct :
//  forall a bst,
//    correct bst -> correct(delete a bst).


//Theorem delete_ismember :
//  forall bst el,
//    correct bst -> isMember el (delete el bst) = false.


//Theorem delete_size :
//  forall bst el,
//    correct bst -> 
//      (isMember el bst = true -> size (delete el bst) = size bst - 1) /\ 
//      (isMember el bst = false -> size (delete el bst) = size bst).


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

//Theorem toList_distinct:
//  forall bst n,
//    correct bst -> 
//    (isMember n bst = true -> only_one (toList bst) n = true) /\
//    (isMember n bst = false -> not_in (toList bst) n = true).


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

//Theorem toList_sorted :
//  forall bst,
//    correct bst -> 
//      sorted (toList bst) = true.


//Theorem list_head_last :
//  forall bst,
//  correct bst ->
//    hd_error (toList bst) = getMin bst /\
//    hd_error (rev (toList bst)) = getMax bst.
}