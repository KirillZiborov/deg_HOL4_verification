# deg_HOL4_verification

Implementation and verification of the [DEG smart contract](https://github.com/cikrf/deg2021/tree/master/contracts) in HOL4 

## Content:

__1) degTypesScript.sml__

Implementation of smart contract types in HOL4.

__2) degScript.sml__

Implementation of smart contract functions in HOL4.

__3) degChainScript.sml__

Framework for embedding a smart contract in an environment model and for specifying its properties in HOL4.

__4) degPropertiesScript.sml__

Proofs of smart contract and its functions properties.

Properties that have been proven

1. Voter authentication in SC.

2. Privacy of intermediate results.

3. The impossibility of sabotage by external violators.
