# Linear Logic for Constructive Mathematics, in Agda

A self-contained implementation of Mike Shulman's “meaning explanation” for his
variant of linear logic, written for the Agda proof assistant.

See the n-category cafe 
[article](https://golem.ph.utexas.edu/category/2018/05/linear_logic_for_constructive.html)
for the meaning explanations, and  [arXiv](https://arxiv.org/abs/1805.07518) for
the paper on linear triposes.

## Usage

The files should typecheck with Agda version 2.5.1 and above. You will need a
reasonably recent version of the relevant parts of the
[standard library](https://github.com/agda/agda-stdlib);
failing that, you will have to supply the definitions of conjunction, 
disjunction and equality manually.

## Contributing

1. Create a fork!
2. Create your feature branch: `git checkout -b my-new-feature`
3. Commit your changes: `git commit -am 'Add some feature'`
4. Push to the branch: `git push origin my-new-feature`
5. Submit a pull request.

## Authors and Contributors

* **Zoltan A. Kocsis** - University of Manchester
* [Shimin Guo](https://github.com/guoshimin)