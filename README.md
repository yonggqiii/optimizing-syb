<a id="readme-top"></a>

<!-- PROJECT SHIELDS -->
<!--
*** I'm using markdown "reference style" links for readability.
*** Reference links are enclosed in brackets [ ] instead of parentheses ( ).
*** See the bottom of this document for the declaration of the reference variables
*** for contributors-url, forks-url, etc. This is an optional, concise syntax you may use.
*** https://www.markdownguide.org/basic-syntax/#reference-style-links
-->
[![Contributors][contributors-shield]][contributors-url]
[![Forks][forks-shield]][forks-url]
[![Stargazers][stars-shield]][stars-url]
[![Issues][issues-shield]][issues-url]
[![MIT License][license-shield]][license-url]
[![LinkedIn][linkedin-shield]][linkedin-url]



<!-- PROJECT LOGO -->
<br />
<div align="center">
<h3 align="center">Recover Your Boilerplate (RYB)</h3>

  <p align="center">
    Optimizing SYB by Recovering Handwritten Traversals
    <br />
    <br />
    <a href="https://github.com/yonggqiii/optimizing-syb/issues/new?labels=bug&template=bug-report---.md">Report Bug</a>
    ·
    <a href="https://github.com/yonggqiii/optimizing-syb/issues/new?labels=enhancement&template=feature-request---.md">Request Feature</a>
  </p>
</div>



<!-- TABLE OF CONTENTS -->
<details>
  <summary>Table of Contents</summary>
  <ol>
    <li>
      <a href="#about">About</a>
    </li>
    <li>
      <a href="#getting-started">Getting Started</a>
      <ul>
        <li><a href="#prerequisites">Prerequisites</a></li>
        <li><a href="#installing-and-building">Installing and Building</a></li>
      </ul>
    </li>
    <li><a href="#usage">Usage</a>
      <ul>
        <li><a href="#basic-usage">Basic Usage</a></li>
        <li><a href="#exposing-unfoldings">Exposing Unfoldings</a></li>
        <li><a href="#plugin-options">Plugin Options</a></li>
      </ul>
    </li>
    <li><a href="#roadmap">Roadmap</a></li>
    <li><a href="#contributing">Contributing</a></li>
    <li><a href="#license">License</a></li>
    <li><a href="#contact">Contact</a></li>
  </ol>
</details>



<!-- ABOUT THE PROJECT -->
## About

https://github.com/user-attachments/assets/d1dd286b-6265-46f3-b1f1-ec6c9d071de5

Recover Your Boilerplate (RYB) is a GHC plugin for optimizing [Scrap Your Boilerplate (SYB)](https://wiki.haskell.org/Scrap_your_boilerplate)-style traversals via specialization, thereby recovering all handwritten boilerplate code. With this plugin, virtually all runtime/space costs associated with using SYB constructs are eliminated by rebuilding handwritten "boilerplate" traversals from SYB-style traversals.

Currently, this plugin supports optimizations for `mkT`, `mkQ`, `mkM` aliases (along with their `ext` variants), and the traversal schemes `everywhere`, `everywhere'`, `everything` and `everywhereM`. Support for other aliases and schemes are in progress.

This plugin has been tested on GHC version 9.4.8. Support for more GHC versions is in progress.

<p align="right">(<a href="#readme-top">back to top</a>)</p>

<!-- GETTING STARTED -->
## Getting Started

This is an example of how you may give instructions on setting up your project locally.
To get a local copy up and running follow these simple example steps.

### Prerequisites
- [GHC](https://www.haskell.org/ghc/) v9.4.8 (base v4.17.2.1)
- [Cabal](https://www.haskell.org/cabal/) v3.10.3.0
- git

### Installing and Building
* Clone this repository
  ```sh
  git clone https://github.com/yonggqiii/optimizing-syb.git
  cd optimizing-syb/
  ```
* Building
  ```sh
  cabal build
  ```
You're all set!

<p align="right">(<a href="#readme-top">back to top</a>)</p>



<!-- USAGE EXAMPLES -->
## Usage
### Basic Usage
This plugin can be used when compiling any source file containing SYB functions. For example:
```haskell
import Data.Company -- A 'Company' datatype that derives Data
import Data.Generics ( everywhere, mkT ) -- SYB functions

incS :: Float -> Salary -> Salary
incS k (S s) = S $ s * (1 + k)

increase :: Data a => Float -> a -> a
increase k = everywhere $ mkT (incS k)
```
To compile with this plugin, specify the `-O2` optimization and the `OptimizingSYB` plugin, like so:
```haskell
{-# OPTIONS_GHC -O2 -fplugin OptimizingSYB #-}
import Data.Company -- A 'Company' datatype that derives Data
import Data.Generics ( everywhere, mkT ) -- SYB functions

incS :: Float -> Salary -> Salary
incS k (S s) = S $ s * (1 + k)

increase :: Data a => Float -> a -> a
increase k = everywhere $ mkT (incS k)
```
However, this plugin will not do anything to this program because no information on the type to specialize `increase` over is provided. Therefore, either specify the exact type that `increase` operates over, such as
```haskell
-- ...
increase :: Float -> Company -> Company -- Specific type for increase
increase k = everywhere $ mkT (incS k)
```
Or write a `SPECIALIZE` pragma:
```haskell
-- ...
increase :: Data a => Float -> a -> a
increase k = everywhere $ mkT (incS k)
{-# SPECIALIZE increase :: Float -> Company -> Company #-}
```

Include the plugin project directory in your `cabal.project` file:
```cabal
packages: .
          -- ...
          /path/to/optimizing-syb
```
Include `optimizing-syb` in your build dependencies in your `my-project.cabal` file:
```cabal
-- ...
executable MyProject
  -- ...
  build-depends:   -- ...
                 , optimizing-syb
                   -- ... 
```
Now you can build your project with `cabal build` and this plugin will optimize your traversals!

### Exposing Unfoldings
An important caveat when using this plugin is that all unfoldings of any used `Data` instances must be included. That is, in the file containing the instance declarations, provide an `-fexpose-all-unfoldings` GHC option:
```haskell
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

import Data.Generics

data Company = C [Dept] deriving (Show, Data)
data Dept = D Name Manager [SubUnit] deriving (Show, Data)
-- ...
```
Otherwise, the plugin may not be able to inline occurrences of `gmapT`, `gmapQ` etc., especially when your datatypes are recursive (GHC does not expose these unfoldings when that is the case):
```haskell
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
data Tree a = Empty | Node (Tree a) a (Tree a) deriving (Show, Data) -- unfoldings for Data (Tree a) are not exposed without
                                                                     -- -fexpose-all-unfoldings option
```
_Note: this requirement affects any data type where `[]` occurs, because GHC does not expose the unfoldings for `Data [a]`. In our testing, re-compiling GHC with the `-fexpose-all-unfoldings` option included in the `Data.Data` source file removes this issue._

### Plugin Options
This plugin does not have customizations, since virtually all passes included are required for optimizing SYB-style traversals. However, this plugin exposes verbosity options to track the transformations applied to the program.

This plugin runs several transformations:
1. Simple optimizations (`--show-simple`): runs a simple preprocessor to inline and simplify invocations of `($)` to reveal applications of SYB schemes
2. Function map extraction (`--show-function-map`): groups `SPECIALIZE`'d functions together for traversal extraction
3. Traversal extraction (`--show-traversal-extraction`): extracts SYB-style traversals as standalone least function for specialization
4. Scheme elimination (`--show-scheme-elim`): eliminates schemes like `everywhere` by turning traversals into recursive functions
5. Traversal specialization (`--show-spec`): specializes traversals
6. Combinator elimination (`--show-gmap-elim`): eliminates calls to combinators like `gmapT` by inlining
7. Type-level evaluation (`--show-type-eval`): eliminates calls to aliases like `mkT` by compile-time type-level evaluation

To see the result of running each phase, provide these flags as options to the `OptimizingSYB` plugin. For example, to show the scheme elimination and combinator elimination passes, you may do something like

```haskell
{-# OPTIONS_GHC -O2 -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--show-scheme-elim #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--show-gmap-elim #-}

import Data.Company -- A 'Company' datatype that derives Data
import Data.Generics ( everywhere, mkT ) -- SYB functions

incS :: Float -> Salary -> Salary
incS k (S s) = S $ s * (1 + k)

increase :: Float -> Company -> Company
increase k = everywhere $ mkT (incS k)
```

<p align="right">(<a href="#readme-top">back to top</a>)</p>



<!-- ROADMAP -->
## Roadmap

- [ ] Support for all SYB features
- [ ] Support for GHC > 9.4.8
- [ ] Support for GHC < 9.4.8

See the [open issues](https://github.com/yonggqiii/optimizing-syb/issues) for a full list of proposed features (and known issues).

<p align="right">(<a href="#readme-top">back to top</a>)</p>



<!-- CONTRIBUTING -->
## Contributing

Contributions are what make the open source community such an amazing place to learn, inspire, and create. Any contributions you make are **greatly appreciated**.

If you have a suggestion that would make this better, please fork the repo and create a pull request. You can also simply open an issue with the tag "enhancement".
Don't forget to give the project a star! Thanks again!

1. Fork the Project
2. Create your Feature Branch (`git checkout -b feature/AmazingFeature`)
3. Commit your Changes (`git commit -m 'Add some AmazingFeature'`)
4. Push to the Branch (`git push origin feature/AmazingFeature`)
5. Open a Pull Request

<p align="right">(<a href="#readme-top">back to top</a>)</p>

### Top contributors:

<a href="https://github.com/yonggqiii/optimizing-syb/graphs/contributors">
  <img src="https://contrib.rocks/image?repo=yonggqiii/optimizing-syb" alt="contrib.rocks image" />
</a>



<!-- LICENSE -->
## License

Distributed under the MIT License. See `LICENSE.txt` for more information.

<p align="right">(<a href="#readme-top">back to top</a>)</p>



<!-- CONTACT -->
## Contact

Foo Yong Qi - yongqi@nus.edu.sg

Project Link: [https://github.com/yonggqiii/optimizing-syb](https://github.com/yonggqiii/optimizing-syb)

<p align="right">(<a href="#readme-top">back to top</a>)</p>


<!-- MARKDOWN LINKS & IMAGES -->
<!-- https://www.markdownguide.org/basic-syntax/#reference-style-links -->
[contributors-shield]: https://img.shields.io/github/contributors/yonggqiii/optimizing-syb.svg?style=for-the-badge
[contributors-url]: https://github.com/yonggqiii/optimizing-syb/graphs/contributors
[forks-shield]: https://img.shields.io/github/forks/yonggqiii/optimizing-syb.svg?style=for-the-badge
[forks-url]: https://github.com/yonggqiii/optimizing-syb/network/members
[stars-shield]: https://img.shields.io/github/stars/yonggqiii/optimizing-syb.svg?style=for-the-badge
[stars-url]: https://github.com/yonggqiii/optimizing-syb/stargazers
[issues-shield]: https://img.shields.io/github/issues/yonggqiii/optimizing-syb.svg?style=for-the-badge
[issues-url]: https://github.com/yonggqiii/optimizing-syb/issues
[license-shield]: https://img.shields.io/github/license/yonggqiii/optimizing-syb.svg?style=for-the-badge
[license-url]: https://github.com/yonggqiii/optimizing-syb/blob/master/LICENSE.txt
[linkedin-shield]: https://img.shields.io/badge/-LinkedIn-black.svg?style=for-the-badge&logo=linkedin&colorB=555
[linkedin-url]: https://linkedin.com/in/fooyongqi
