#  Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
#  See https://llvm.org/LICENSE.txt for license information.
#  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

from ..common import Clock, Input, Output
from ..constructs import ControlReg, Wire
from ..module import Module, generator
from ..system import System
from ..types import UInt, bit, types, Bits
from .. import esi

from .common import AxiMMIO

import glob
from io import FileIO
import pathlib
import shutil

__dir__ = pathlib.Path(__file__).parent


def XrtBSP(user_module):
  """Use the Xilinx RunTime (XRT) shell to implement ESI services and build an
  image or emulation package.
  How to use this BSP:
  - Wrap your top PyCDE module in `XrtBSP`.
  - Run your script. This BSP will write a 'build package' to the output dir.
  This package contains a Makefile.xrt which (given a proper Vitis dev
  environment) will compile a hw image or hw_emu image. It is a free-standing
  build package -- you do not need PyCDE installed on the same machine as you
  want to do the image build.
  - To build the `hw` image, run 'make -f Makefile.xrt TARGET=hw'. If you want
  an image which runs on an Azure NP-series instance, run the 'azure' target
  (requires an Azure subscription set up with as per
  https://learn.microsoft.com/en-us/azure/virtual-machines/field-programmable-gate-arrays-attestation).
  This target requires a few environment variables to be set (which the Makefile
  will tell you about).
  - To build a hw emulation image, run with TARGET=hw_emu.
  - The makefile also builds a Python plugin. To specify the python version to
  build against (if different from the version ran by 'python3' in your
  environment), set the PYTHON variable (e.g. 'PYTHON=python3.9').
  """

  XrtMaxAddr = 2**24
  id_width = 4
  axi_width = 64
  addr_width = 64

  class XrtTop(Module):
    ap_clk = Clock()
    ap_resetn = Input(Bits(1))

    # AXI4-Lite slave interface
    s_axi_control_AWVALID = Input(Bits(1))
    s_axi_control_AWREADY = Output(Bits(1))
    s_axi_control_AWADDR = Input(Bits(20))
    s_axi_control_WVALID = Input(Bits(1))
    s_axi_control_WREADY = Output(Bits(1))
    s_axi_control_WDATA = Input(Bits(32))
    s_axi_control_WSTRB = Input(Bits(32 // 8))
    s_axi_control_ARVALID = Input(Bits(1))
    s_axi_control_ARREADY = Output(Bits(1))
    s_axi_control_ARADDR = Input(Bits(20))
    s_axi_control_RVALID = Output(Bits(1))
    s_axi_control_RREADY = Input(Bits(1))
    s_axi_control_RDATA = Output(Bits(32))
    s_axi_control_RRESP = Output(Bits(2))
    s_axi_control_BVALID = Output(Bits(1))
    s_axi_control_BREADY = Input(Bits(1))
    s_axi_control_BRESP = Output(Bits(2))

    @generator
    def construct(ports):
      System.current().platform = "xrt"

      rst = ~ports.ap_resetn

      xrt = AxiMMIO(
          esi.MMIO,
          appid=esi.AppID("xrt_mmio"),
          clk=ports.ap_clk,
          rst=rst,
          awvalid=ports.s_axi_control_AWVALID,
          awaddr=ports.s_axi_control_AWADDR,
          wvalid=ports.s_axi_control_WVALID,
          wdata=ports.s_axi_control_WDATA,
          wstrb=ports.s_axi_control_WSTRB,
          arvalid=ports.s_axi_control_ARVALID,
          araddr=ports.s_axi_control_ARADDR,
          rready=ports.s_axi_control_RREADY,
          bready=ports.s_axi_control_BREADY,
      )

      # AXI-Lite control
      ports.s_axi_control_AWREADY = xrt.awready
      ports.s_axi_control_WREADY = xrt.wready
      ports.s_axi_control_ARREADY = xrt.arready
      ports.s_axi_control_RVALID = xrt.rvalid
      ports.s_axi_control_RDATA = xrt.rdata
      ports.s_axi_control_RRESP = xrt.rresp
      ports.s_axi_control_BVALID = xrt.bvalid
      ports.s_axi_control_BRESP = xrt.bresp

      user_module(clk=ports.ap_clk, rst=rst)

      # Copy additional sources
      sys: System = System.current()
      sys.add_packaging_step(esi.package)
      sys.add_packaging_step(XrtTop.package)

    @staticmethod
    def package(sys: System):
      """Assemble a 'build' package which includes all the necessary build
      collateral (about which we are aware), build/debug scripts, and the
      generated runtime."""

      from jinja2 import Environment, FileSystemLoader, StrictUndefined

      sv_sources = glob.glob(str(__dir__ / '*.sv'))
      tcl_sources = glob.glob(str(__dir__ / '*.tcl'))
      for source in sv_sources + tcl_sources:
        shutil.copy(source, sys.hw_output_dir)

      env = Environment(loader=FileSystemLoader(str(__dir__)),
                        undefined=StrictUndefined)
      makefile_template = env.get_template("Makefile.xrt.j2")
      dst_makefile = sys.output_directory / "Makefile.xrt"
      dst_makefile.open("w").write(
          makefile_template.render(system_name=sys.name))
      template = env.get_template("xrt_package.tcl.j2")
      dst_package_tcl = sys.hw_output_dir / "xrt_package.tcl"
      dst_package_tcl.open("w").write(
          template.render(system_name=sys.name, max_mmio_size=XrtMaxAddr))

      shutil.copy(__dir__ / "xrt.ini", sys.output_directory / "xrt.ini")
      shutil.copy(__dir__ / "xsim.tcl", sys.output_directory / "xsim.tcl")

  return XrtTop
