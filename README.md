# Abstract Interpreters for Free

- Trying to implement the methods explained in the paper for analysis of LambdaCal
- Not sure where to start.

## 0-CFA

CFA is Control Flow Analysis and 0-CFA is the one variant one it which uses no "context".

### How does it work?
- So you store your variables inside store with a reference in the environment to location in store.
- You also store the kontinuations inside the store and keep a pointer of the most recent kont available.
- So now, how do you analyse this.

- Static analysis means, you approximate running the program and taking all the `possible` branches in the program.
- You have control flow graph for the program, now static analysis means you want to look at all the paths of the program.
- But how do you go about looking at all the paths of the program.
- You start with a initial state and create a list of all the states that a state could step to.
- Now you have a bunch of states you want to explore, then do the same and then do it again.
- This is just like searching a graph, well because we are, and it's special name is control flow graph.
- Well and at the end you will have all the values the program can possibly take, or ranges of values that program can take.

- Let's think about how this work with a simple program:
``` python

```



#### What the Widening?
- Widening is a technique where 
