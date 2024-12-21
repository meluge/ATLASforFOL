# ATLAS
This is the prototype implementation of the paper *Constrained LTL Specifications Learning from Examples* published in ICSE 2025. Preprint available at: https://arxiv.org/abs/2412.02905.

This repository contains the source code, the executable, and the benchmark problems and results as presented in the paper.

## Provenance
- A preprint of the paper is available at: https://arxiv.org/abs/2412.02905.
- The source code of ATLAS is available at: https://github.com/cmu-soda/ATLAS.
- The latest executable of ATLAS is available at the GitHub release page: https://github.com/cmu-soda/ATLAS/releases.

## Setup using Docker (Recommend)
We suggest using Docker to test our tool.

### From dockerhub (Easiest way)
We have made the image available on dockerhub:
```
docker pull changjianzhangcmu/atlas
docker run -it --rm changjianzhangcmu/atlas
```

Run Atlas inside Docker container:
```
java -cp bin/Atlas.jar cmu.s3d.ltl.app.CLIKt -f benchmark/5to10Traces/0000.trace
```
The output should look like:
```
filename,numOfPositives,numOfNegatives,maxNumOfOP,numOfVariables,maxLengthOfTraces,expected,solvingTime,formula
benchmark/5to10Traces/0000.trace,5,5,3,2,5,"[G(!(x0))]",0.36,"!(F(x0))"
```

### Build from local
1. Clone the repo and download the latest executable:
    ```
    git clone https://github.com/cmu-soda/ATLAS.git
    cd ATLAS
    mkdir bin
    # download from the release page, e.g., v1.0.2
    wget https://github.com/cmu-soda/ATLAS/releases/download/v1.0.2/Atlas.jar -O bin/Atlas.jar
    ```

2. Build the Docker image:
    ```
    docker build -t atlas .
    ```

3. Run the Docker image:
    ```
    docker run -it --rm atlas
    ```

## Local Setup
Download the latest release of Atlas.jar from the *[Releases](https://github.com/cmu-soda/ATLAS/releases)* page.

### Requirements
The program requires Java >= 8 to run. We have tested the program with Java 8 and Ubuntu 22.04.

**Note:**
The tool requires AlloyMax to run. AlloyMax will copy some util modules and solvers to a temp directory. In some cases, AlloyMax may complain it cannot find those modules and solvers. In such situations, I suggest cloning the repo to your local machine and manually start AlloyMax for the first time.
```
git clone https://github.com/cmu-soda/ATLAS.git
cd ATLAS
java -jar lib/AlloyMax-1.0.3.jar
```
Click the *Execute* button on the GUI. It should find an instance, which indicates that Alloy can successfully run on your machine. Then, you can close the AlloyMax GUI. This should demonstrate your computer is able to run AlloyMax.

**Note:**
However, the above step may not be necessary because explicitly providing the library path using `-Djava.library.path` can let AlloyMax successfully find the third-party libraries such as OpenWBO.

### Run ATLAS
We suggest downloading the latest ATLAS executable to the `bin` folder under the root of this repo:
```
# under the root of this repo (i.e., ATLAS)
mkdir bin
# download from the release page, e.g., v1.0.2
wget https://github.com/cmu-soda/ATLAS/releases/download/v1.0.2/Atlas.jar -O bin/Atlas.jar
```

You can now test it with a sample file from our benchmark:
```
java -cp bin/Atlas.jar cmu.s3d.ltl.app.CLIKt -f benchmark/5to10Traces/0000.trace
```
The output should look like:
```
filename,numOfPositives,numOfNegatives,maxNumOfOP,numOfVariables,maxLengthOfTraces,expected,solvingTime,formula
benchmark/5to10Traces/0000.trace,5,5,3,2,5,"[G(!(x0))]",0.305,"!(F(x0))"
```

You can also choose to use OpenWBO as the backend MaxSAT solver:
```
java -Djava.library.path=./lib -cp bin/Atlas.jar cmu.s3d.ltl.app.CLIKt -f benchmark/5to10Traces/0000.trace -s OpenWBOWeighted
```

**Note:**
This repo only provides the OpenWBO MaxSAT solver for linux-amd64. Thus, to use OpenWBO, it needs to run on a Linux amd64 machine. It is possible to use it inside the Docker image. However, a known issue is that the performance of OpenWBO is dramatically slow in Docker container when using a Mac as the host machine.


## Usage
The key to use our tool is to provide a trace containing the example traces. We extend the problem format from [samples2LTL](https://github.com/ivan-gavran/samples2LTL) to define a problem. The file looks like:
```
0,0;0,1;0,1;0,0;0,0::0
0,1;0,1;0,1;0,1;0,1::4
0,0;0,1;0,1;0,1;0,1::3
0,1;0,1;0,0;0,1;0,1::4
0,0;0,0;0,0;0,1;0,0::2
---
1,0;1,1;1,0;1,1;0,0::1
0,0;1,1;1,0;0,1;0,1::0
1,0;1,0;0,1;0,1;0,1::3
0,1;0,0;0,1;1,0;0,1::2
1,0;0,1;1,0;1,0;1,1::3
---
G,F,!,U,&,|,->,X
---
2
---
G(!(x0))
---
<optional constraints and objectives in AlloyMax spec>
```
The first part is the positive traces. Each trace is a sequence of states. Each state is a sequence of atom values `0,0` separated by `,`. States in a trace is separated by `;`. The last `::` indicates after the last state of the trace, where it would go back to for the infinite loop in a lasso trace. When it is omitted, it means the trace goes back to the first state.

For example: `0,0;0,0;0,0;0,1;0,0::2` means there are 5 states in the trace, and after the last state, it will go back to the trace with index 2. The index starts from 0.

The second part is the negative traces.

The third part is the operators to allow in the learned formula. In total, we allow `&, |, ->, !, X, G, F, U`.

The next part is a number that indicates the depth of the syntax tree. However, we are actually using a DAG to model the syntax. So we need the max number of nodes in the graph. For simplicity, we compute the max number of nodes as `2^depth - 1`. So in practice, set the depth to be less or equal to 4, which will allow a maximum of 15 subformulas in the learned LTL.

In addition, a user can also use brackets e.g., `[3]` to enforce the max number of nodes.

The next part is the expected formula. **Multiple expected formulas are separated by `;`. This is optional.**

The final part is an optional constraints and objectives in AlloyMax spec. Syntax for Alloy can be found [here](https://alloytools.org/documentation.html). E.g., the following Alloy expressions constraint that the formula should be `G p` and `p` should be of negation normal form.
```
fact {
    root in G
    all n: Neg | n.l in Literal // negation normal form
}
```

### Usage options
The usage of our tool is as follows:
```
Usage: Atlas [OPTIONS]

  A tool to learn LTL formulas from a set of positive and negative examples by
  using AlloyMax.

Options:
  --_run TEXT          Run the learning process. YOU SHOULD NOT USE THIS.
                       INTERNAL USE ONLY.
  -s, --solver TEXT    The AlloyMax solver to use. Default: SAT4JMax
  -f, --filename TEXT  The file containing one task to run.
  -t, --traces TEXT    The folder containing the tasks to run. It will find
                       all task files under the folder recursively.
  -T, --timeout INT    The timeout in seconds for solving each task.
  -m, --model          Print the model to use for learning.
  -A, --findAny        Find any solution. Default: false
  -e, --expected       Enumerate until the expected formula found.
  -h, --help           Show this message and exit
```

For example, to run a particular task file. Note that, the task file should be ending with `.trace`. Then, you can do:
```
java -Djava.library.path=./lib -cp LTL-Learning.jar cmu.s3d.ltl.app.CLIKt -f <the trace file> -s OpenWBOWeighted -T 60
```
In this example, we use `-Djava.library.path=./lib/open-wbo` to add the open-wbo MaxSAT Solver by Ruben Martins to the path, and we use `OpenWBOWeighted` as the solving algorithm. This is recommended because it is the fastest one from our benchmark.

The result of the above example task file should look like:
```
<trace file path>,5,5,2,2,5,"G(!(x0))",0.495,"!(F(x0))"
```

**Note:** The learned LTL might be different from the expected one for two reasons: (1) they are actually equal like "G(!x0) <=> !F(x0)"; (2) there exists a smaller LTL formula satisfying the examples traces. You can use the `-e` or `-expected` option to let the solver enumerate the solutions until an expected one (as defined in the trace file) is found.

## Benchmark
The benchmark problems are located in the `benchmarks` folder. The results are located in the `benchmark_results` folder.

You can use the following script to run problems under a folder:
```
ls benchmark/<problem folder> | xargs -I {} java -Djava.library.path=./lib -cp bin/Atlas.jar cmu.s3d.ltl.app.CLIKt -f benchmark/<problem folder>/{} -s OpenWBOWeighted -T 180
```

## Data
The `benchmark_results` folder contains the results (in `.csv` files) for our benchmark as presented in the paper. We also provide a Jupyter notebook file `data_summary.ipynb` for summarizing the results as shown in the table and figure in our paper.
