.. Edh documentation master file,

Welcome to Đ (Edh)'s documentation!
===================================

.. toctree::
   :maxdepth: 2
   :caption: Contents:


Code Snippets
-------------

Sample code::

   {#
    # dynamic scoped effects
    #   -- an imperative counterpart of functional monads
    #
    # with mathematical methodologies, monads is a mature and powerful machinery
    # best implemented in a functional programming language, to vend and consume
    # provisional effects with well defined contexts.
    # (there is algebraic effects & handlers under active development at time
    # of speaking - 2020)
    #
    # with procedural methodologies, such contextual semantics of APIs are
    # largely ended up defined and consulted as specifications in descriptive
    # documentation form, in lieu of language constructs to encode the
    # applicability of certain effects contextual-wise.
    #
    # *dynamic scoped effects* essentially is *dynamic scoping* with a separate
    # effect registration & resolution space, avoided the failure of traditional
    # dynamic scoping that lexical artifacts get mixed with callstack provided
    # artifacts, which has things confusingly messed up.
    #
    #}


   # %{ # technical basics

   # %% #
   method effectfulHello() {
     console.print$ 'Hello, ' ++ perform userName ++ '!'
   }

   method effectfulConsumer() {
     effect userName = 'world'

     effectfulHello()
   }

   # %% # run it
   effectfulConsumer()

   # %} # end of technical basics


   # %{ # mockup a services & applications framework

   # %% # simple mockup of a user record

   data User( id_, name ) pass


Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
