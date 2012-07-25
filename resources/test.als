abstract sig Element {color: set Color}
abstract sig Color{}

one sig e1, e2 extends Element{}
one sig red, blue extends Color{}

fact fact1{
	some el1: Element | red in el1.color
	some el2: Element | blue in el2.color
}

run{}
//this/Element.color[e1$0, red$0]
