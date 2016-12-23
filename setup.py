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
      version          = "1.0rc6",
      author           = "Simon BUSARD, Xavier GILLARD",
      author_email     = "simon.busard@uclouvain.be, xavier.gillard@uclouvain.be",
      url              = "http://lvl.info.ucl.ac.be/Tools/PyNuSMV",
      description      = "Tools, examples and experiments that showcase the potential uses for PyNuSMV",
      packages         = find_packages(),
      install_requires = ['pynusmv'],
      entry_points     = {
        'console_scripts' : [
            'ctl=pynusmv_tools.ctl.CTLcheck:main',
            'fairctl=pynusmv_tools.fairctl.FairCTLcheck:main',
            'ctlk=pynusmv_tools.ctlk.cmd.cmd:main',
            'arctl=pynusmv_tools.arctl.cmd.trace:main',
            'tlace=pynusmv_tools.tlace.tlace:main',
            # MAS
            'atl=pynusmv_tools.atl.check:main',
            'atlk_fo=pynusmv_tools.atlkFO.check:main',
            'atlk_po=pynusmv_tools.atlkPO.check:main',
            # utils
            'smv2dot=pynusmv_tools.dotDump:main',
            'smv_cmp=pynusmv_tools.compare:main',
            # BMC tools
            'diagnos=pynusmv_tools.diagnosability:main',
            # LTL BMC - directly using NuSMV api to generate the problem (fastest)
            'bmc_ltl=pynusmv_tools.bmcLTL.bmc_ltl:main',
            # LTL BMC - using the lower interface functions to generate the
            # problem (close to a performance tie with alternative1 + most flexible
            # implementation)
            'bmc_ltl_li=pynusmv_tools.bmcLTL.bmc_ltl_li:main',
            # LTL BMC - not using apis from pynusmv.bmc.*
            'bmc_ltl_py=pynusmv_tools.bmcLTL.bmc_ltl_py:main'
        ]
      },
      # TESTS
      test_suite='nose.collector',
      tests_require=['nose']
)
