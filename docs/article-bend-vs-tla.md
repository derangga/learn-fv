# TLA+ vs. Bend 2: Two tools, two ways to verify a system

We used two formal verification tools to check the same two small systems: TLA+, with the TLC model checker, and Bend 2, a programming language with a built-in proof checker.

We wanted to answer two practical questions: How much work does each tool take, and what does a successful check actually tell us?

Here is what we found:

- On the same machine, Bend checks finished in seconds. TLC checks took minutes.
- Both tools caught almost every deliberate bug we introduced.
- TLC could not finish the full-size models we wanted to check. Bend did not have the same model-size limit.
- Bend required more code and proof work, but we reached a first complete pass sooner.
- A successful check means something different in each tool.

These results come from two small safety systems. They do not show that one tool is better for every project.

## Why verify a system?

Most teams test software by running it against cases they expect to happen. A test checks one scenario and compares the result with what the team expects.

That approach works well for known cases. But some bugs appear only after an unusual sequence of events.

Consider a payment system. A client sends a charge request, but the network delivers it twice. The service saves the charge and then crashes before it can reply. The client retries the request. Each event may be harmless on its own. In the wrong order, they can charge the customer twice.

A test catches this bug only if someone writes a test for that exact sequence.

Formal verification gives us another way to look for these problems. We describe a system and state the rules it must follow. Then a tool checks those rules across many possible event sequences, or checks a proof that a rule always holds.

For example, we might state that an order must never be charged twice. A verification tool can explore how retries, duplicate messages, delays, and crashes interact.

We think this matters even more when an AI agent writes the code. Reading generated code is not enough to establish that it behaves correctly. A precise rule, checked by a verification tool, gives us stronger evidence.

Our project asks a practical question: If an AI agent writes both the system description and the verification work, how much effort do two different tools take, and what do their results tell us?

## Two tools, two approaches

TLA+ and Bend 2 aim to help us reason about system behavior. They take different approaches.

To make that difference concrete, imagine a counter. Each button press adds one, but the counter stops at 10. Our rule is simple: the counter must never exceed 10.

### TLA+ and the TLC model checker

TLA+ is a language for describing a system in terms of states and transitions.

A state is a snapshot of the system. For our counter, a state might be "the counter shows 3". A transition describes how the system moves from one state to another. Here, pressing the button changes the counter.

We describe the initial state, the possible transitions, and the rules that must always hold. TLC then checks the model.

TLC is a model checker. It starts from the initial state and explores every possible transition within the model's limits. It checks the rules as it visits each state.

If TLC finds a violation, it reports a counterexample trace: the sequence of steps that led to the bad state. For our counter, TLC visited 11 states, from 0 through 10, and found no violation.

You can think of TLC as someone walking through every room in a building, using a floor plan you provide. It checks every room in that plan, but it cannot check rooms the plan leaves out.

That floor plan has limits. In TLA+, we call them bounds. A bound might limit the number of orders, duplicate messages, or clock ticks in a model.

Larger bounds create more states for TLC to explore. The number of states can grow very quickly, so a model that finishes at small bounds may become too large to check at full size.

### Bend 2

Bend 2 takes a different approach. It is a programming language with a proof checker built in.

Instead of searching for a bad state, you write a law: a statement that must always hold. Then you write a proof, which gives a step-by-step argument for that law.

For our counter, the law might say: "After any list of button presses, the counter is at most 10." Bend's checker examines the proof and accepts or rejects it.

A law written this way does not depend on a model-size limit. It can describe any number of button presses. If the checker accepts a correct proof, the law holds for all of them.

Two conditions matter here. First, the law must describe the behavior we actually care about. Second, the checker must be sound.

A law that is too weak can let bugs pass. In an early test, we wrote laws that only said the counter must never exceed its limit. Those laws accepted two buggy counter implementations. We later added laws that described the exact result of each step.

Bend 2 is new. Its checker has a standard mode and a stronger mode that rechecks results with a small kernel proven in Lean. We took every measurement with the standard mode. We ran the stronger mode once afterward, on the final proofs (see "What a pass means" below).

### A term we use in the results

A *mutant* is a copy of a system with one deliberate bug added. We use mutants to see whether a verification tool catches known problems. We try to introduce the same bug in each tool's version of the system.

## How we compared the tools

We built two small systems in both tools and gave them the same rules.

We measured:

- how long each check took;
- what happened when we increased the model size;
- how many deliberate bugs each tool caught;
- how much work it took to write each model and proof.

One AI agent wrote the models, laws, and proofs. The next section describes the systems we used.

## The two systems

Both systems are safety systems. A safety rule says that something bad must never happen.

### Payment system

An order service and a payment provider exchange messages. The system allows messages to be retried, duplicated, or delayed. It also includes refunds, crashes, and restarts.

We checked two rules:

- an order must never be charged twice;
- a refund must never exceed the original charge.

### Stock reservation system

Customers can reserve stock, confirm a reservation, or let it expire. The system includes a clock, and messages can arrive more than once or out of order.

We checked three rules:

- stock counts must always add up;
- an expired reservation must return its stock exactly once;
- an expired reservation must never be confirmed.

## What we measured

We ran the checks on two machines:

- **2-core VPS:** 2 CPU cores, about 1.9 GB of RAM, running Linux.
- **MacBook M4:** Apple M4 chip, 10 CPU cores, and 16 GiB of memory.

We compare timings only when the checks ran on the same machine. Do not compare the VPS results directly with the MacBook results.

### Check times on the 2-core VPS

| Check | Tool | Time | Runs |
|---|---|---:|---:|
| Payment | Bend | 6.484 s | Average of 5 runs |
| Stock | Bend | 2.358 s | Average of 10 runs |
| Payment, one order | TLC | 5 min 01 s | 1 run |
| Stock, reduced limits | TLC | 348.943 s | 1 run |

These are measured times. Each TLC result comes from one run, so we do not calculate a timing ratio.

### Check times on the MacBook M4

| Check | Tool | Time | Runs |
|---|---|---:|---:|
| Payment, one order | TLC | 23 s | 1 run |
| Stock, reduced limits | TLC | 28 s | 1 run |
| All Bend checks together | Bend | 5 s | 1 run |

The 5-second Bend run includes both systems, 14 false-statement tests, and the mutant runs. We did not measure Bend separately for each file on this machine. This table therefore does not provide a direct timing comparison between the tools.

### What happened at full size?

TLC did not finish either full-size model.

Here is what happened during each run:

- **Payment on the VPS:** We ran the model with two orders for 62 minutes, then stopped it manually. TLC had visited 9,079,945 distinct states and had found no violation. The agent estimated that a complete run might require exploring between \(10^{11}\) and \(10^{12}\) states. That figure is an estimate, not a measurement.
- **Stock on the VPS:** We stopped the run after 60 minutes. TLC had visited 25,051,664 distinct states.
- **Stock on the MacBook M4:** The run lasted about 48 minutes and reached 149,567,238 distinct states. Its store of visited states used 86 GB and filled the disk. We had not set a disk limit or monitored the remaining space.

A run that we stop does not tell us whether the rule holds. It only tells us that TLC had not found a violation before we stopped it.

We therefore reduced the model limits so TLC could finish:

- For payment, we used one order instead of two.
- For stock, we used fewer IDs, one product, and a smaller clock. We tested duplicate messages in a separate run.

Both reduced models finished without an error. But they covered fewer cases than the full-size models.

### How many deliberate bugs did the tools catch?

| System | Mutants | Bend | TLC at full-size limits |
|---|---:|---:|---:|
| Payment | 6 | 6 of 6 | 6 of 6 |
| Stock | 10 | 9 of 9 | 9 of 10 |

The stock system has one mutant without a Bend version. Bend's number type truncates at zero, so we could not represent that bug in Bend.

TLC did not find a violation for one other stock mutant during a 15-minute run at the full-size limits. It found the bug at a smaller limit when duplicate messages were enabled.

TLC produced counterexample traces with 2 to 11 states. At full-size limits, it found each bug it caught in 5 seconds to 3 minutes and 29 seconds on the VPS. Some payment runs shared the VPS's two CPU cores, which increased their running times.

### How much work did writing take?

The AI agent estimated the writing times. A human author may need more or less time.

| Measure | Payment TLA+ | Payment Bend | Stock TLA+ | Stock Bend |
|---|---:|---:|---:|---:|
| Writing time | About 15 min | About 35 min | About 25 min | About 50 min |
| Lines | 444 | 3,660 | 428 | 3,145 |
| Failed attempts | 0 failed model checks | 12 failed proof runs, limit 15 | 2 failed model checks | 14 failed proof runs, limit 15 |
| Time to first complete pass | About 64 min | About 31 min | About 91 min | 49 min 44 s |

We calculated the time to the first complete pass from recorded timestamps. TLA+ times include the time spent waiting for TLC. Our records do not show the order in which all runs happened.

The Bend versions contain about 7 to 8 times as many lines as the TLA+ versions. We calculated that range from the line counts above.

## What does a successful check mean?

A successful check does not mean the same thing in both tools.

### A successful TLC run

A TLC pass means that no state within the model's configured limits breaks the rules.

It does not cover states outside those limits. For example, a successful payment check with one order tells us nothing about how two orders interact.

### A successful Bend proof

A Bend pass means the checker accepted a proof of the stated law. If the law describes the behavior we care about and the checker is sound, the claim holds for every possible input covered by that law.

Both conditions matter. A proof can be valid while proving a weaker claim than we intended.

We took every measurement with Bend's standard checker. Bend also offers a stronger recheck, `--verdict`, that uses a small kernel proven in Lean. It could not run in our sandbox because Lean was missing. Afterward we ran it on a MacBook with Lean 4.34.0, on the same UC1 and UC2 proof files, and both printed `ALL PROOFS CHECK`. A Bend pass here therefore does not rest on the standard checker alone. It still depends on the laws saying what we meant. We did not run the stronger recheck on the mutants.

We also gave Bend 14 statements that we knew were false. It rejected all 14, with and without `--verdict`. Both runs print the same failure message, so the test does not show whether the kernel rejects anything the standard checker accepts. It is useful, but it does not prove that the checker is sound.

There are two more limits to keep in mind:

- A Bend proof covers our Bend version of the system. It does not prove that the Go services themselves behave correctly.
- We ran 500 random event sequences per system through both implementations, and their results agreed. This is a test, not a proof.

Our early tests also showed why the laws need to be precise. Laws that only set an upper limit let two buggy counter implementations pass. We added laws that state the exact result of each event.

## Where each tool helped, and where it struggled

### TLC: useful counterexamples, limited scale

TLC was especially useful when we wanted to see how a bug could happen.

For example, a payment implementation without a duplicate-message check produced a trace that showed an order being placed, a message being duplicated, and the message being delivered twice.

TLC also found shallow bugs in seconds to minutes, even when it could not finish checking a clean model.

Its main limitation was model size:

- The number of states grew quickly as we added orders, IDs, duplicate messages, and clock ticks.
- Reduced limits meant less coverage. The payment model no longer had two orders at once. The stock model no longer combined several IDs, products, and quantities with duplicate messages.
- Two runs filled a disk.

### Bend: fast checks, broad claims

Bend checks finished quickly on the VPS, taking between 2.358 and 6.484 seconds.

Its laws can cover any number of orders and any list of events. This avoids the state explosion we encountered with TLC.

But writing and maintaining the proofs took more work:

- **Failures were harder to diagnose.** Bend reports the first failing proof step. A rejection tells us where the proof stopped checking, but it does not provide a counterexample that shows how the system fails.
- **We had to write missing number facts.** Bend's standard library lacked some of the arithmetic facts our stock proofs needed. We wrote about 130 lines for number facts and another 160 lines for list sums and records. One lemma alone took about 450 lines.
- **Proofs required manual work.** Bend has no tactics, so we wrote each proof by hand. About 70% of the payment proof text came from temporary scripts that the agent generated but that we did not keep.
- **Small model changes caused proof changes.** A data type change affected the hand-written cases. One mutant needed new events, which caused every matching case in the proofs to fail until we updated them.

## Limits of this experiment

These results need context. We tested only two small safety systems, and several parts of the experiment limit what we can conclude:

- One AI agent wrote everything. It used one shared description to write both the TLA+ rules and the Bend laws. The same misunderstanding could therefore appear in both versions. This is our inference, not something we measured.
- All writing times are estimates from the agent.
- TLC could not finish the full-size models, so some results use reduced limits.
- Most timing results come from a single run.
- The mutants match in intent, not line for line. One stock mutant has a simplified Bend version.
- We did not test liveness properties, which describe whether something good eventually happens.
- We did not test a lease system with a fencing token.

These results do not tell us how either tool performs on those untested systems or properties.

## Which tool should you use?

Our recommendation is to start with TLA+ when you want to explore whether a design can break.

TLC gives you a counterexample trace that shows the sequence of events behind a violation. Changing a model or a rule is also relatively cheap in our experience, although we did not measure the time needed for rule changes.

Consider Bend when you need a claim to hold for every list of events and can afford to write and maintain the proof. In our experiment, that meant owning about 3,000 lines of proof text for each system.

You can also use both when the system is important enough to justify the extra work. They offer different kinds of evidence, and our experiment found that their main difference was the cost of producing that evidence.

## What we would test next

There are several questions we could not answer in this experiment:

- **A lease system with a fencing token:** We want to see how both tools handle this design.
- **Liveness properties:** We want to check whether the tools can verify that something good eventually happens.
- **More on Bend's stronger recheck:** We ran it once on the two final proofs. We want to run it on the mutants and test whether it rejects anything the standard checker accepts.
- **Human authoring time:** We want to compare how long experienced human authors take to write each model and proof.
- **Rule changes:** We want to measure the cost of changing a rule in each tool.

Those tests would help us understand where each approach fits beyond the two safety systems in this experiment.
