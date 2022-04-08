# Getting Started with Lean 4

Launch a new terminal window. Use the pwd command to confirm that you are "in" the top-level directory for this class (so far), namely /workspaces/teaching. The use 
"cd .." to make /workspaces your current directory. Continue by running each of the following shell commands in turn. The final command should print "Hello, World!"

```sh
mkdir robot
cd robot
elan self update
elan override set leanprover/lean4:stable
lake init robot
lake build
build/bin/robot
```

If you got "Hello, World!" you've got an up and running Lean4 project. 

To edit that new project, first close the current folder (File > Close Folder) but be advised that this window will disappear, so read on first. After you close this project, use File > Open Folder to open your new project folder at /workspaces/robot. Open a terminal in this new project, then do "lake clean", "lake build", and run the binary you'll find in build/robot/bin. You should get "Hello, World!" You are now up and running with a Lean4 project. Both projects use the same underlying VM. I have configured it to support both Lean 3 and Lean 4 projects. Shortly I wlil provide you a a new project, like this one, but with the contents of Galois Joe's Lean 4 robot controller code installed.