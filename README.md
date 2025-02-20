# 💯 Full Specification Project for Smart Contracts

> The goal of this project is to obtain a way to fully specify smarts contracts to make sure it is never possible to steal or block user funds.

Project page: [🌲&nbsp;formal.land/docs/tools/coq-of-solidity/specification-project](https://formal.land/docs/tools/coq-of-solidity/specification-project)

## 1️⃣ First Step: Full Specification of ERC-20

Let us say we have our Domain Specific Language in [Rocq](https://rocq-prover.org/) (using the Rocq language plus a set of axioms for the primitives we need) to specify Solidity smart contracts. We can go in two directions:

1. Building a way to prove a smart contract written in this DSL to be equivalent to an actual Solidity smart contract, using as input the Rocq translation of a smart contract through the [coq-of-solidity](https://github.com/formal-land/coq-of-solidity) translator. This should be doable but is not a priority as it will be more about proof engineering than about researching new specification techniques.
2. Building a general specification to express that the smart contract is safe. This is what we will be working on.

The ERC-20 standard smart contract is used to represent the ownership of fungible tokens (that exist in multiple versions), in other words virtual coins. They are many similar implementations, but the one we will take is the one from OpenZeppelin [github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/token/ERC20/ERC20.sol](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/token/ERC20/ERC20.sol).
