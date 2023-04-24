Contributing to the library
===========================

Thank you for your interest in contributing to the Agda standard library.
Hopefully this guide should make it easy to do so! Feel free to ask any
questions on the Agda mailing list. Before you start please read the
[style-guide](https://github.com/agda/agda-stdlib/blob/master/notes/style-guide.md).

What is an acceptable contribution?
===================================

- The contribution should be useful in a diverse set of areas.

- The bar for accepting contributions that use the FFI to depend on external
  (i.e. Haskell, JavaScript) packages is much higher.

- If the same concept already exists in the library, there needs to be a *very* good
  reason to add a different formalisation.

- There should be evidence that the code works. Usually this will be proofs, but sometimes
  for purely computational contributions this will involve adding tests.

- It should use the minimal set of Agda features, i.e. it should normally use
  the Agda option pragmas `--cubical-compatible` and `--safe`, with the occasional use of
  `--with-K`, `--sized`, `--guardedness` in certain situations.

In general, if something is in a general undergraduate Computer Science or Mathematics
textbook it is probably (!) contributable.

Setup
=====

The typical workflow when contributing to the standard library's repository
is to interact with two remote versions of the repository:

1. agda/agda-stdlib, the official one from which you can pull updates so that
   your contributions end up on top of whatever the current state is.

2. USER/agda-stdlib, your fork to which you can push branches with contributions
   you would like to merge

This tutorial guides you to set up a local copy of agda-stdlib so that you can
start contributing. Once things are set up properly,  you can stick to only
steps 5., 6., 7., 8. and 9. for future contributions.

1. Fork the agda-stdlib repository
----------------------------------

Go to https://github.com/agda/agda-stdlib/ and click the 'Fork' button in the
top right corner. This will create a copy of the repository under your username.
We assume in the rest of this document that this username is 'USER'.

2. Double check-line ending settings if not on Linux
----------------------------------------------------

If you are on a Mac, make sure that your git options has `autocrlf` set  to `input`.
This can be done by executing
```
git config --global core.autocrlf input
```
If you are on Windows, make sure that your editor can deal with Unix format files.

3. Obtain a local copy of agda/agda-stdlib
------------------------------------------

Obtain a local copy of the agda-stdlib repository. Here we are going to retrieve
it from the `agda/agda-stdlib` repository so that `master` always points to the
state the official library is in.

```shell
git clone git@github.com:agda/agda-stdlib
```

**NB**:
  if you have not added a public key to your github profile to set up
  git over ssh, you may need to use the https url instead of the git@ one
  (`https://github.com/agda/agda-stdlib`)


4. Add your fork as a secondary remote
--------------------------------------

As we have mentioned earlier the idea is to pull updates from `agda/agda-stdlib`
and to push branches to your fork. For that to work you will need to explain to
git how to refer to your fork. This can be done by declaring a remote like so
(again you may need to use the https url if you haven't configured git over ssh)

```shell
git remote add USER git@github.com:USER/agda-stdlib
```

You can check that this operation succeeded by fetching this newly added remote.
Git should respond with a list of branches that were found on your fork.

```shell
git fetch USER
```

***End of initial setup. When creating a future PRs one should start here.***.

5. Create a branch for your new feature
---------------------------------------

Now that we have a local copy, we can start working on our new feature.
The first step is to make sure we start from an up-to-date version of the
repo by synchronising `master` with its current state on `agda/agda-stdlib`.

```shell
git checkout master
git pull
```

The second step is to create a branch for that feature based off of `master`.
Make sure to pick a fresh name in place of `new_feature`. We promptly push
this new branch to our fork using the `-u` option fo `push`.

```shell
git checkout -b new_feature
git push USER -u new_feature
```

6. Make your changes
--------------------

You can then proceed to make your changes. Please follow existing
conventions in the library, see
[style-guide](https://github.com/agda/agda-stdlib/blob/master/notes/style-guide.md).
for details. Document your changes in `agda-stdlib-fork/CHANGELOG.md`.

If you are creating new modules, please make sure you are having a
proper header, and a brief description of what the module is for, e.g.
```
------------------------------------------------------------------------
-- The Agda standard library
--
-- {PLACE YOUR BRIEF DESCRIPTION HERE}
------------------------------------------------------------------------
```

If possible, each module should use the options `--safe` and
`--cubical-compatible`. You can achieve this by placing the following
pragma under the header and before any other line of code (including
the module name):
```
{-# OPTIONS --cubical-compatible --safe #-}
```

If a module cannot be made safe or needs the `--with-K` option then it should be
split into a module which is compatible with these options and an auxiliary
one which will either be called `SOME/PATH/Unsafe.agda` or `SOME/PATH/WithK.agda`
or explicitly declared as either unsafe or needing K in `GenerateEverything.hs`

7. [ Optional ] Run test suite locally
--------------------------------------

**NB** this step is optional as these tests will be run automatically
by our CI infrastructure when you open a pull request on Github, but it
can be useful to run it locally to get a faster turn around time when finding
problems.

Ensure your changes are compatible with the rest of the library by running
the commands
```
make clean
make test
```
inside the `agda-stdlib-fork` folder. Continue to correct any bugs
thrown up until the tests are passed. Note that the tests
require the use of a tool called `fix-whitespace`. See the
instructions at the end of this file for how to install this.

8. Add, commit and push your changes to your fork
-------------------------------------------------

Use the `git add X` command to add changes to file `X` to the commit,
or `git add .` to add all the changed files.

Run the command `git commit` and enter a meaningful description for
your changes.

Upload your changes to your fork by running `git push`.

9. Open a PR
------------

Once you're satisfied with your additions, you can make sure they have been
pushed to the feature branch by running

```shell
git status
```

and making sure there is nothing left to commit or no local commits to push.
You should get something like:

```
On branch new_feature
Your branch is up-to-date with 'USER/new_feature'.

nothing to commit, working tree clean
```

You can then go to `https://github.com/agda/agda-stdlib/pulls`, click on
the green 'New pull request' button and then the 'compare across forks' link.

You can then select your fork as the 'head repository' and the corresponding
feature branch and click on the big green 'Create pull request' button. The
library maintainers will then be made aware of your requested changes and
should be in touch soon.

10. Update the PR
------------------

If after opening a PR you realise you have forgotten something, or have received
a review asking you to change something, you can simply push more commits to the
branch and they will automatically be added to the PR.


How to enforce whitespace policies
----------------------------------

### Installing fix-whitespace

This tool is kept in the main agda organization. It can be installed by
following these instructions:
   ```
   git clone https://github.com/agda/fix-whitespace --depth 1
   cd fix-whitespace/
   cabal install
   ```

### Adding fix-whitespace as a pre-commit hook

You can add the following code to the file `.git/hooks/pre-commit` to
get git to run fix-whitespace before each `git commit` and ensure
you are never committing anything with a whitespace violation:

   ```
   #!/bin/sh

   fix-whitespace --check
   ```

Type-checking the README directory
----------------------------------

* By default the README directory is not exported in the
  `standard-library.agda-lib` file in order to avoid clashing with other people's
  README files. This means that by default type-checking a file in the README
  directory fails.

* If you wish to type-check a README file, then you will need to change the line:
  ```
  include: src
  ```
  to
  ```
  include: src .
  ```
  in the `standard-library.agda-lib` file.

* Please do not include this change in your pull request.


Continuous Integration (CI)
===========================

Updating the Haskell-CI workflow
--------------------------------

The file `.github/workflows/haskell-ci.yml` tests building the helpers specified in `agda-stdlib-utils.cabal`.
It is autogenerated by the tool [haskell-ci]
but has some custom modification which need to be restored after each regeneration of this workflow.

[haskell-ci] creates the workflow file from settings in the `cabal.haskell-ci` file
and from the contents of the `tested-with` field in the `agda-stdlib-utils.cabal` file.
After updating this field, run the following:
```
haskell-ci regenerate
patch --input=.github/haskell-ci.patch .github/workflows/haskell-ci.yml
```

[haskell-ci]: https://github.com/haskell-CI/haskell-ci
