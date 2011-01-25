#!/usr/bin/env python

from distutils.core import setup

setup(name='air-reasoner',
      version='0.5',
      description='Reasoning Engine for the AIR Language',
      author='Decentralized Information Group @ MIT',
      author_email='pipian@mit.edu',
      url='http://dig.csail.mit.edu/hg/air-reasoner/',
      packages=['airreasoner', 'airreasoner.sparql'],
      )
