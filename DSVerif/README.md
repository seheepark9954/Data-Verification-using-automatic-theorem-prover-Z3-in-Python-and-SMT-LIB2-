# DSVerif -- A formal data set verification tool.
This repository contains the information for a formal data set verification tool, as descried in our [paper](https://arxiv.org/abs/2009.10822).

The directory [properties](./properties) contains example properties in the [*SMT-LIB*](http://smtlib.cs.uiowa.edu/) language. Those properties are the following:
- [balanced](./properties/balanced) -- a formula that checks that the data set has a balanced set of labels
- [contradicting](./properties/contradicting) -- a formula that checks that the data set has no contradicting labels (same input vectors, different expected outputs)
- [min\_100\_ex](./properties/min_100_ex) -- a formula that checks if there are at least 100 training examples
- [min\_max](./properties/min_max) -- a formula that checks if the data set input values are normalized within a min / max range ([-1,1])
- [well\_distributed](./properties/well_distributed) -- a formula that checks that there doesn't exist a point which is more distant than a given constant (1) w.r.t. all the data set training examples

Currently, the data set verification tool's source code is not publicly available. If you are interested in the tool or collaboration, please do not hesitate to [contact us](mailto:jorge.lopez-c@airbus.com,maxime.labonne@airbus.com,claude.poletti@airbus.com?subject=Regarding%20the%20data%20set%20verification%20tool...). A small video showcasing the tool is shown in the video below.

https://user-images.githubusercontent.com/5852134/127121795-4f4f3413-0b18-42f6-a8f6-6cba307cf54e.mp4
