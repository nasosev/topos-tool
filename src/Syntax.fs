/// Convenient syntax definitions.
[<AutoOpen>]
module Syntax

type Product = Product
    with
        static member (?<-)(Product, C, D) = Category.product C D
        static member (?<-)(Product, f, g) = Morphism.product f g
        static member (?<-)(Product, F, G) = Presheaf.product F G
        static member inline (?<-)(Product, a, b) = a * b

let inline (*) a b = (?<-) Product a b

type Sum = Sum
    with
        static member (?<-)(Sum, C, D) = Category.sum C D
        static member (?<-)(Sum, f, g) = Morphism.sum f g
        static member (?<-)(Sum, F, G) = Presheaf.sum F G
        static member inline (?<-)(Sum, a, b) = a + b

let inline (+) a b = (?<-) Sum a b

type Compose = Compose
    with
        static member (?<-)(Compose, f, g) = Morphism.compose f g
        static member (?<-)(Compose, P, Q) = Functor.compose P Q
        static member inline (?<-)(Compose, a, b) = a @ b

let inline (@) a b = (?<-) Compose a b

let inline (^) F G = Presheaf.exp G F
let inline (==) F G = Presheaf.isIso F G
