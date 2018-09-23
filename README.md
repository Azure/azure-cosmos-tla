# High-level TLA+ specifications for the five consistency levels offered by Azure Cosmos DB

Customers of Azure Cosmos DB can associate any number of [Azure regions](https://azure.microsoft.com/en-us/global-infrastructure/regions/) (50+ at the time of writing) to their Cosmos database, at any time. The clients can read and write locally with any of the regions associated with the given Cosmos database. Here we describe the consistency guarantees provided to the clients by [Cosmos DB](http://cosmosdb.com) that empowers them take full advantage of Azure's many regions.

## Overview

Cosmos DB allows developers to choose between [five well-defined consistency models](https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels) along the consistency spectrum – _strong_, _bounded staleness_, _session_, _consistent prefix_ and _eventual_. Cosmos DB has operationalized and exposed them to developers with clear semantics, performance/availability tradeoffs and backed by comprehensive [Service Level Agreements (SLAs)](https://azure.microsoft.com/en-us/support/legal/sla/cosmos-db/). Informally, the five consistency models are described as below.

| Consistency Level | Guarantees                                                                                  |
| ----------------- | ------------------------------------------------------------------------------------------- |
| Strong            | Linearizable reads                                                                          |
| Bounded Staleness | Consistent Prefix. Reads lag behind writes by k prefixes or t interval                      |
| Session           | Consistent Prefix. Monotonic reads, monotonic writes, read-your-writes, write-follows-reads |
| Consistent Prefix | Updates returned are some prefix of all the updates, with no gaps                           |
| Eventual          | Eventual                                                                                    |

Describing the consistency levels in English is prone to errors due to the ambiguity of natural language and generalizations involved. In this document, we use [TLA+ specification language](http://lamport.azurewebsites.net/tla/tla.html) to specify the consistency guarantees precisely. TLA+ is a tool for specifying distributed algorithms/protocols mathematically and model checking them for correctness. The Cosmos DB engineering team heavily relies on TLA+ for specifying distributed algorithms and protocols mathematically and model checking them for correctness to verify the design decisions and address the corner cases induced by concurrency and faults. [Here]((https://aka.ms/LeslieMM)) is a recent video interview of Dr. Leslie Lamport describing the application of TLA+ in Cosmos DB. 

[![](Lamport.png)](https://aka.ms/LeslieMM)

Although Cosmos DB is a globally distributed database, it provides the user with a single logical system image of all of their globally distributed data. The specifications we provide in this document focus on the clients' interactions with their globally distributed Cosmos DB database as a single logical entity by performing writes and reads, based on the consistency level specified. We refrain from modeling the Cosmos DB internals, and model a user's Cosmos DB database as a single system image, abstracting away the underlying global distribution/replication among the regions.

To simplify the exposition of the consistency guarantees given to the clients, we provide three simple scenarios accompanied by their TLA+ specifications. The first two (Scenario 1 and Scenario 2), we consider a single client interacting with the Cosmos database. These examples also give a gentle introduction to TLA+ and, more accurately, to its companion language [PlusCal](https://lamport.azurewebsites.net/tla/pluscal.html), which provides a pseudocode-like interface to the TLA+ specifications. In the final example (the general model), we present our TLA+/PlusCal specification of the general model of Cosmos DB, where multiple clients across different regions put Cosmos DB to the test with respect to the consistency guarantees it provides in the presence of concurrent read and writes.

## Scenarios

- [Scenario 1: TLA+ for a client writing incremented counter values](scenario1/README.md)
- [Scenario 2: TLA+ for a client Reading, incrementing, writing-back counter values](scenario2/README.md)
- [The general model: TLA+ for the general model with multiple clients operating on a globally distributed Cosmos database](general-model/README.md)

## Questions

If you have any questions, please reach out to dharmas@microsoft.com.

## License

[MIT](./LICENSE)
