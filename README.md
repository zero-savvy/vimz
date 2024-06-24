# __VIMz__: Verifiable Image Manipulation via Folding-based zkSNARKs
<p align="center">
  <img width="100%" src="cover.png" alt="Generated by AI (Freepik.com)">
  <em>Cover generated by <a href="https://www.freepik.com"> FreePik </a></em>
</p>



VIMz is currently (Dec. 2023) the fastest and most efficient program to proof authenticity of transformed/editted images w.r.t. an original source. It is built on top of [NOVA](https://github.com/microsoft/Nova) recursive zkSNARKs with the front-end of [Nova-Scotia](https://github.com/nalinbhardwaj/Nova-Scotia) (using [Circom](https://github.com/iden3/circom) language for defining internal circuits).
The protocol supports image resolutions of up to 4K (3840 x 2160) and higher.

## Installation
### I-Prerequisites

#### I-a) For Installing Node JS:

``` curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.3/install.sh | bash ```

``` source ~/.bashrc ```

``` nvm install v16.20.0 ```

> [!NOTE]
> in rare cases (miss-configured Linux distros), if you got an error stating that version "v16.20.0" was not found; following command might help:
> ``` export NVM_NODEJS_ORG_MIRROR=http://nodejs.org/dist ```
> 

#### I-b) For installing snarkjs:

``` npm install -g snarkjs ```

#### I-c) For installing Rust:
```curl --proto ’=https’ --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain none -y```

#### I-d) Additional build-essential libraries and packages:
```sudo apt install gcc```

```sudo apt install build-essential nlohmann-json3-dev libgmp3-dev nasm```

#### I-e) For installing Circom:
```git clone https://github.com/iden3/circom.git```

```cd circom```

```cargo build --release```

```cargo install --path circom```

### II-Installing VIMz
Once you have installed dependencies, you can proceed with setting up and running VIMz. To obtain the latest version of VIMz, clone its GitHub repository using the following command:

```git clone https://github.com/zero-savvy/vimz.git```

#### II-a) Installing VIMz itself

Head to the ```nova``` directory:
cd vimz/nova

build and install ```vimz``` using ```cargo```:

```cargo build```

```cargo install --path .```

verify installation of ```vimz```:

```vimz --help```

#### II-b) Building Circuits
go to the circuits directory:

```cd vimz/circuits```

build ZK circuits using the provided script in this directory:

```./build-circuits.sh```


## How to Use
```
vimz --function <FUNCTION>
--resolution <RESOLUTION> --input <FILE>
--circuit <R1CS FILE> --output <FILE>  
--witnessgenerator <BINARY/WASM FILE>
```

## Bnwchmarks
We've built the tools necessary for benchmarking using the samples provided in the ```samples``` directory. To do this, 
simply Go to the main directory of vimz repo and run any number of transformations as you prefer using the provided script:

```
./benchmark.sh [list-of-transformations]

```

__Example 1__: benchmarking a single transformation:

```
./benchmark.sh contrast
     or
./benchmark.sh blur
     or
./benchmark.sh grayscale
```

__Example 2__: benchmarking parallel execution of multiple transformations:

```
./benchmark.sh contrast blur
     or
./benchmark.sh resize blur shapness
```

> [!NOTE]
> Since the proof generation process can be time consuming, it is recommended to initially benchmark with only one transformation at a time~(replicating the results presented in Table IV of the paper). Once these results are verified, you can proceed to run multiple transformations in parallel to replicate the results shown in Table V.

__Sample output__: The script generates a file (or multiple files, one per given transformation) with a ```.output``` suffix in the same directory. These files contain the standard output of running the ```vimz``` command directly, as shown in Figure below. The output includes various performance metrics. The total proof generation time can be calculated as the sum of two numbers: ```RecursiveSNARK creation``` and ```CompressedSNARK::prove:``` from the output.

<p align="center">
  <img width="100%" src="sample-output.png" alt="output">
  <em>VIMz STD output</em>
</p>


## Acknowledgement
1. We thank [@iden3](https://github.com/iden3) for building the awesome [Circom](https://github.com/iden3/circom) language and provding the [CircomLib](https://github.com/iden3/circomlib).
2. This work currently heavily relies on [Nova-Scotia](https://github.com/nalinbhardwaj/Nova-Scotia)'s compiler for transforming Circom circuits to the ones comptible with [Nova](https://github.com/microsoft/Nova).
3. The very early version of the project (solely based on Circom without NOVA) was inspired by image transformation proofs from [@TrishaDatta](https://github.com/TrishaDatta)'s Circom circuits [repository](https://github.com/TrishaDatta/circom-circuits),<br>
which were related to the [medium post](https://medium.com/@boneh/using-zk-proofs-to-fight-disinformation-17e7d57fe52f) By Trisha Datta and Dan Boneh.

## License
<p xmlns:cc="http://creativecommons.org/ns#" >This work is licensed under <a href="http://creativecommons.org/licenses/by-nc/4.0/?ref=chooser-v1" target="_blank" rel="license noopener noreferrer" style="display:inline-block;">Attribution-NonCommercial 4.0 International 
 <img style="height:22px!important;margin-left:3px;vertical-align:text-bottom;" src="https://mirrors.creativecommons.org/presskit/icons/cc.svg?ref=chooser-v1"><img style="height:22px!important;margin-left:3px;vertical-align:text-bottom;" src="https://mirrors.creativecommons.org/presskit/icons/by.svg?ref=chooser-v1"><img style="height:22px!important;margin-left:3px;vertical-align:text-bottom;" src="https://mirrors.creativecommons.org/presskit/icons/nc.svg?ref=chooser-v1"></a></p>
