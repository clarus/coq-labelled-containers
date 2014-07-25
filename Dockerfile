FROM ubuntu
MAINTAINER Guillaume Claret

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y gcc make git

# OCaml
RUN apt-get install -y ocaml camlp4-extra

# Coq trunk
WORKDIR /root
RUN git clone https://github.com/coq/coq.git
WORKDIR /root/coq
RUN yes "" |./configure
RUN make -j2
RUN make install

# Compile the project
ADD . /root/coq-labelled-containers
WORKDIR /root/coq-labelled-containers
RUN ./configure.sh
RUN make