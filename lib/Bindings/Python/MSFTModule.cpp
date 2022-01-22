//===- MSFTModule.cpp - MSFT API pybind module ----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "DialectModules.h"

#include "circt-c/Dialect/MSFT.h"
#include "circt/Dialect/MSFT/MSFTAttributes.h"
#include "circt/Support/LLVM.h"

#include "mlir/Bindings/Python/PybindAdaptors.h"
#include "mlir/CAPI/IR.h"
#include "mlir/CAPI/Support.h"

#include "PybindUtils.h"
#include <pybind11/functional.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
namespace py = pybind11;

using namespace circt;
using namespace circt::msft;
using namespace mlir::python::adaptors;

static py::handle getPhysLocationAttr(MlirAttribute attr) {
  return py::module::import("circt.dialects.msft")
      .attr("PhysLocationAttr")(attr)
      .release();
}

class PrimitiveDB {
public:
  PrimitiveDB(MlirContext ctxt) { db = circtMSFTCreatePrimitiveDB(ctxt); }
  ~PrimitiveDB() { circtMSFTDeletePrimitiveDB(db); }
  bool addPrimitive(MlirAttribute locAndPrim) {
    return mlirLogicalResultIsSuccess(
        circtMSFTPrimitiveDBAddPrimitive(db, locAndPrim));
  }
  bool isValidLocation(MlirAttribute loc) {
    return circtMSFTPrimitiveDBIsValidLocation(db, loc);
  }

  CirctMSFTPrimitiveDB db;
};

class PlacementDB {
public:
  PlacementDB(MlirOperation top, PrimitiveDB *seed) {
    db = circtMSFTCreatePlacementDB(top, seed ? seed->db
                                              : CirctMSFTPrimitiveDB{nullptr});
  }
  ~PlacementDB() { circtMSFTDeletePlacementDB(db); }
  size_t addDesignPlacements() {
    return circtMSFTPlacementDBAddDesignPlacements(db);
  }
  bool addPlacement(MlirAttribute loc, MlirAttribute path, std::string subpath,
                    MlirOperation op) {
    return mlirLogicalResultIsSuccess(circtMSFTPlacementDBAddPlacement(
        db, loc,
        CirctMSFTPlacedInstance{path, subpath.c_str(), subpath.size(), op}));
  }
  py::object getInstanceAt(MlirAttribute loc) {
    CirctMSFTPlacedInstance inst;
    if (!circtMSFTPlacementDBTryGetInstanceAt(db, loc, &inst))
      return py::none();
    std::string subpath(inst.subpath, inst.subpathLength);
    return (py::tuple)py::cast(std::make_tuple(inst.path, subpath, inst.op));
  }
  py::handle getNearestFreeInColumn(CirctMSFTPrimitiveType prim,
                                    uint64_t column, uint64_t nearestToY) {
    MlirAttribute nearest = circtMSFTPlacementDBGetNearestFreeInColumn(
        db, prim, column, nearestToY);
    if (!nearest.ptr)
      return py::none();
    return getPhysLocationAttr(nearest);
  }
  void walkPlacements(
      py::function pycb,
      std::tuple<py::object, py::object, py::object, py::object> bounds,
      py::object prim, py::object walkOrder) {

    auto handleNone = [](py::object o) {
      return o.is_none() ? -1 : o.cast<int64_t>();
    };
    int64_t cBounds[4] = {
        handleNone(std::get<0>(bounds)), handleNone(std::get<1>(bounds)),
        handleNone(std::get<2>(bounds)), handleNone(std::get<3>(bounds))};
    CirctMSFTPrimitiveType cPrim;
    if (prim.is_none())
      cPrim = -1;
    else
      cPrim = prim.cast<CirctMSFTPrimitiveType>();

    CirctMSFTWalkOrder cWalkOrder;
    if (!walkOrder.is_none())
      cWalkOrder = walkOrder.cast<CirctMSFTWalkOrder>();
    else
      cWalkOrder = CirctMSFTWalkOrder{CirctMSFTDirection::NONE,
                                      CirctMSFTDirection::NONE};

    circtMSFTPlacementDBWalkPlacements(
        db,
        [](MlirAttribute loc, CirctMSFTPlacedInstance p, void *userData) {
          std::string subpath(p.subpath, p.subpathLength);
          py::gil_scoped_acquire gil;
          py::function pycb = *((py::function *)(userData));
          auto physLoc = getPhysLocationAttr(loc);
          if (!p.op.ptr) {
            pycb(physLoc, py::none());
          } else {
            pycb(physLoc, std::make_tuple(p.path, subpath, p.op));
          }
        },
        cBounds, cPrim, cWalkOrder, &pycb);
  }

private:
  CirctMSFTPlacementDB db;
};

/// Populate the msft python module.
void circt::python::populateDialectMSFTSubmodule(py::module &m) {
  mlirMSFTRegisterPasses();

  m.doc() = "MSFT dialect Python native extension";

  m.def("get_instance", circtMSFTGetInstance, py::arg("root"), py::arg("path"));

  py::enum_<PrimitiveType>(m, "PrimitiveType")
      .value("M20K", PrimitiveType::M20K)
      .value("DSP", PrimitiveType::DSP)
      .value("FF", PrimitiveType::FF)
      .export_values();

  py::enum_<CirctMSFTDirection>(m, "Direction")
      .value("NONE", CirctMSFTDirection::NONE)
      .value("ASC", CirctMSFTDirection::ASC)
      .value("DESC", CirctMSFTDirection::DESC)
      .export_values();

  mlir_attribute_subclass(m, "PhysLocationAttr",
                          circtMSFTAttributeIsAPhysLocationAttribute)
      .def_classmethod(
          "get",
          [](py::object cls, PrimitiveType devType, uint64_t x, uint64_t y,
             uint64_t num, std::string subPath, MlirContext ctxt) {
            auto cSubPath = mlirStringRefCreateFromCString(subPath.c_str());
            return cls(circtMSFTPhysLocationAttrGet(ctxt, (uint64_t)devType, x,
                                                    y, num, cSubPath));
          },
          "Create a physical location attribute", py::arg(),
          py::arg("dev_type"), py::arg("x"), py::arg("y"), py::arg("num"),
          py::arg("sub_path") = py::str(""), py::arg("ctxt") = py::none())
      .def_property_readonly(
          "devtype",
          [](MlirAttribute self) {
            return (PrimitiveType)circtMSFTPhysLocationAttrGetPrimitiveType(
                self);
          })
      .def_property_readonly("x",
                             [](MlirAttribute self) {
                               return circtMSFTPhysLocationAttrGetX(self);
                             })
      .def_property_readonly("y",
                             [](MlirAttribute self) {
                               return circtMSFTPhysLocationAttrGetY(self);
                             })
      .def_property_readonly("num", [](MlirAttribute self) {
        return circtMSFTPhysLocationAttrGetNum(self);
      });

  mlir_attribute_subclass(m, "PhysicalBoundsAttr",
                          circtMSFTAttributeIsAPhysicalBoundsAttr)
      .def_classmethod(
          "get",
          [](py::object cls, uint64_t xMin, uint64_t xMax, uint64_t yMin,
             uint64_t yMax, MlirContext ctxt) {
            auto physicalBounds =
                circtMSFTPhysicalBoundsAttrGet(ctxt, xMin, xMax, yMin, yMax);
            return cls(physicalBounds);
          },
          "Create a PhysicalBounds attribute", py::arg("cls"), py::arg("xMin"),
          py::arg("xMax"), py::arg("yMin"), py::arg("yMax"),
          py::arg("context") = py::none());

  mlir_attribute_subclass(m, "PhysicalRegionRefAttr",
                          circtMSFTAttributeIsAPhysicalRegionRefAttr)
      .def_classmethod(
          "get",
          [](py::object cls, std::string name, MlirContext ctxt) {
            auto physicalBounds = circtMSFTPhysicalRegionRefAttrGet(
                ctxt, mlirStringRefCreateFromCString(name.c_str()));
            return cls(physicalBounds);
          },
          "Create a PhysicalRegionRef attribute", py::arg("cls"),
          py::arg("name"), py::arg("context") = py::none());

  py::class_<PrimitiveDB>(m, "PrimitiveDB")
      .def(py::init<MlirContext>(), py::arg("ctxt") = py::none())
      .def("add_primitive", &PrimitiveDB::addPrimitive,
           "Inform the DB about a new placement.", py::arg("loc_and_prim"))
      .def("is_valid_location", &PrimitiveDB::isValidLocation,
           "Query the DB as to whether or not a primitive exists.",
           py::arg("loc"));

  py::class_<PlacementDB>(m, "PlacementDB")
      .def(py::init<MlirOperation, PrimitiveDB *>(), py::arg("top"),
           py::arg("seed") = nullptr)
      .def("add_design_placements", &PlacementDB::addDesignPlacements,
           "Add the placements already present in the design.")
      .def("add_placement", &PlacementDB::addPlacement,
           "Inform the DB about a new placement.", py::arg("location"),
           py::arg("path"), py::arg("subpath"), py::arg("op"))
      .def("get_nearest_free_in_column", &PlacementDB::getNearestFreeInColumn,
           "Find the nearest free primitive location in column.",
           py::arg("prim_type"), py::arg("column"), py::arg("nearest_to_y"))
      .def("get_instance_at", &PlacementDB::getInstanceAt,
           "Get the instance at location. Returns None if nothing exists "
           "there. Otherwise, returns (path, subpath, op) of the instance "
           "there.")
      .def("walk_placements", &PlacementDB::walkPlacements,
           "Walk the placements, with possible bounds. Bounds are (xmin, xmax, "
           "ymin, ymax) with 'None' being unbounded.",
           py::arg("callback"),
           py::arg("bounds") =
               std::make_tuple(py::none(), py::none(), py::none(), py::none()),
           py::arg("prim_type") = py::none(),
           py::arg("walk_order") = py::none());

  py::class_<CirctMSFTWalkOrder>(m, "WalkOrder")
      .def(py::init<CirctMSFTDirection, CirctMSFTDirection>(),
           py::arg("columns") = CirctMSFTDirection::NONE,
           py::arg("rows") = CirctMSFTDirection::NONE);
}
