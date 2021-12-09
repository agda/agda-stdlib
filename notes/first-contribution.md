How to contribute a first PR to agda-stdlib
===========================================

The typical workflow when contributing with the standard library's repository
is to interact with two remote versions of the repository:

1. agda/agda-stdlib, the official one from which you can pull updates so that
   your contributions end up on top of whatever the current state is.

2. USER/agda-stdlib, your fork to which you can push branches with contributions
   you would like to merge

This tutorial guides you to setup a local copy of agda-stdlib so that you can
start contributing. Once things are set up properly,  you can stick to only
steps 4., 5. and 6. for future contributions.

1. Fork the agda-stdlib repository
----------------------------------

Go to https://github.com/agda/agda-stdlib/ and click the 'Fork' button in the
top right corner. This will create a copy of the repository under your username.
We assume in the rest of this document that this username is 'USER'.

2. Obtain a local copy of agda/agda-stdlib
------------------------------------------

Obtain a local copy of the agda-stdlib repository. Here we are going to retrieve
from the `agda/agda-stdlib` repository so that `master` always points to the
state the official library is in.

```shell
git clone git@github.com:agda/agda-stdlib
```

**NB**:
  if you have not added a public key to your github profile to set up
  git over ssh, you may need to use the https url instead of the git@ one
  (`https://github.com/agda/agda-stdlib`)


3. Add your fork as a secondary remote
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

4. Create a branch for your new feature
---------------------------------------

Now that we have a local copy, we can start working on our new feature.
The first step is to make sure we start from an up-to-date version of the
repo by synchronising `master` with its current state on `agda/agda-stdlib`.

```shell
git checkout master
git pull
```

The second step is to create a branch for that feature based off of `master`.
We promptly push this new branch to our fork.

```shell
git checkout -b new_feature
git push USER -u new_feature
```

You can then proceed to make your changes, use `git add`, `git commit`, and
`git push` to add them.

5. Open a PR
------------

Once you're satisfied with your additions, you can make sure they have been
pushed to the feature branch by running

```shell
git status
```

and making sure there is nothing left to commit or no local commits to push.
You should get

```
On branch new_feature
Your branch is up-to-date with 'USER/new_feature'.

nothing to commit, working tree clean
```

You can then go to `https://github.com/agda/agda-stdlib/pulls`, click on
the green 'New pull request' button and then the 'compare across forks' link.

You can then select your fork as the 'head repository' and the corresponding
feature branch and click on the big green 'Create pull request' button.

6. Updating the PR
------------------

If after opening a PR you realise you have forgotten something or have received
a review asking you to change something, you can simply push more commits to the
branch and they will automatically be added to the PR.
