'''
# This script provides all the necessary logic for you to build a distribution
# of pynusmv-tools which you can run on your machine.
#
# This file is part of the pynusmv-tools distribution. As such it is licensed to you
# under the term of the LGPLv2. For more information regarding the legal aspect
# of this licensing, please refer to the full text of the license on the free
# software foundation website.
#
# Author: X. Gillard <xavier.gillard [at] uclouvain.be>
'''
from setuptools import setup, find_packages

setup(name             = 'pynusmv-tools',
      version          = "1.0rc3",
      author           = "Simon BUSARD, Xavier GILLARD",
      author_email     = "simon.busard@uclouvain.be, xavier.gillard@uclouvain.be",
      url              = "http://lvl.info.ucl.ac.be/Tools/PyNuSMV",
      description      = "Tools, examples and experiments that showcase the potential uses for PyNuSMV",
      packages         = find_packages(),
      install_requires = ['pynusmv']
)
