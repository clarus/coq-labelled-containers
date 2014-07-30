FROM ubuntu
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git

# OCaml and Coq
RUN apt-get install -y --no-install-recommends ocaml camlp4-extra coq

# coq-ext-lib
WORKDIR /root
RUN git clone https://github.com/coq-ext-lib/coq-ext-lib.git
WORKDIR /root/coq-ext-lib
RUN make && make install

# Compile the project
ADD . /root/coq-labelled-containers
WORKDIR /root/coq-labelled-containers
CMD ./configure.sh && make