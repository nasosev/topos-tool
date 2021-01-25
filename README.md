# _topos-tool_
Computational tool for tiny presheaf topoi.

version: prerelease

---

## how to
- fsharp
  - you will need fsharp installed:
    - [linux](https://fsharp.org/use/linux/)
    - [mac](https://fsharp.org/use/mac/)
    - [win](https://fsharp.org/use/windows/)
    - [freebsd](https://fsharp.org/use/freebsd/)
- building
  - in the root directory, build by entering at your terminal:
    ```
    dotnet build -c release
    ```
- notebooks
  - this program is intended to be used in `.ipynb` notebook files within visual studio code or jupyter. see https://github.com/dotnet/interactive for details on how to set this up.
  - examples are in the directory "nb".
- tests
  - in the root directory, run tests by entering at your terminal:
    ```
    dotnet fsi test/Test.fsx
    ```
## features
- latex output
- categories
  - binary products/sums
  - category of elements
- presheaves
  - yoneda embedding
  - binary products/sums
  - pullbacks/pushouts
  - equalisers/coequalisers
  - exponentials
  - isomorphisms
- truth objects
- biheyting algebra of subobjects
  - meets/joins
  - implication/subtraction
  - negation/supplement
  - boundary/coboundary
  - quantifiers
- lawvere-tierney topologies

## to do
- comma categories
- general limits/colimits
- modal operators
- internal logic
- geometric and logical morphisms
- j-sheaves
- ...


## references
- Marie La Palme Reyes, Gonzalo E. Reyes, Houman Zolfaghari, _Generic figures and their glueings. A constructive approach to functor categories_, Polimetrica (2008), ISBN: 8876990046. [pdf](https://marieetgonzalo.files.wordpress.com/2004/06/generic-figures.pdf).
- Saunders Mac Lane, Ieke Moerdijk, _Sheaves in geometry and logic. A first introduction to topos theory_, Springer-Verlag (1994), ISBN: 0-387-97710-4.

## acknowledgements
- thanks to the awesome f# community at [fsharp.slack.com](http://fsharp.slack.com) for their guidance.
