#include "geometry_interface.hpp"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <limits>
#include <queue>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace geometry {
namespace {

constexpr std::uint32_t invalid_point = static_cast<std::uint32_t>(-1);
constexpr std::size_t invalid_tet = static_cast<std::size_t>(-1);
constexpr std::array<std::array<std::uint8_t, 2>, 6> tet_edges{{
    {{0, 1}}, {{0, 2}}, {{0, 3}}, {{1, 2}}, {{1, 3}}, {{2, 3}},
}};
constexpr std::array<std::array<std::uint8_t, 3>, 4> tet_faces{{
    {{1, 2, 3}}, {{0, 2, 3}}, {{0, 1, 3}}, {{0, 1, 2}},
}};

struct EdgeKey {
    std::uint32_t a = 0;
    std::uint32_t b = 0;
    EdgeKey() = default;
    EdgeKey(std::uint32_t first, std::uint32_t second)
        : a(std::min(first, second)), b(std::max(first, second)) {}
    bool operator==(const EdgeKey& other) const noexcept {
        return a == other.a && b == other.b;
    }
};

struct EdgeHash {
    std::size_t operator()(const EdgeKey& edge) const noexcept {
        return std::hash<std::uint64_t>{}(
            (static_cast<std::uint64_t>(edge.a) << 32U) | edge.b);
    }
};

struct FaceKey {
    std::array<std::uint32_t, 3> ids{};
    explicit FaceKey(std::array<std::uint32_t, 3> value) : ids(value) {
        std::sort(ids.begin(), ids.end());
    }
    bool operator==(const FaceKey& other) const noexcept {
        return ids == other.ids;
    }
};

struct FaceHash {
    std::size_t operator()(const FaceKey& face) const noexcept {
        std::size_t value = face.ids[0];
        value ^= face.ids[1] + 0x9e3779b9U + (value << 6U) + (value >> 2U);
        value ^= face.ids[2] + 0x9e3779b9U + (value << 6U) + (value >> 2U);
        return value;
    }
};

struct Crossing {
    std::array<std::uint32_t, 3> face{};
    Point3d point{};
    double parameter = 0.0;
    std::array<double, 3> barycentric{};
    bool coplanar_edge_hit = false;
    EdgeKey coplanar_edge{};
};

Point3d add(const Point3d& lhs, const Point3d& rhs) {
    return {lhs.x + rhs.x, lhs.y + rhs.y, lhs.z + rhs.z};
}

Point3d subtract(const Point3d& lhs, const Point3d& rhs) {
    return {lhs.x - rhs.x, lhs.y - rhs.y, lhs.z - rhs.z};
}

Point3d multiply(const Point3d& point, double scale) {
    return {point.x * scale, point.y * scale, point.z * scale};
}

double dot(const Point3d& lhs, const Point3d& rhs) {
    return lhs.x * rhs.x + lhs.y * rhs.y + lhs.z * rhs.z;
}

Point3d cross(const Point3d& lhs, const Point3d& rhs) {
    return {
        lhs.y * rhs.z - lhs.z * rhs.y,
        lhs.z * rhs.x - lhs.x * rhs.z,
        lhs.x * rhs.y - lhs.y * rhs.x,
    };
}

double squared_length(const Point3d& value) {
    return dot(value, value);
}

double distance(const Point3d& lhs, const Point3d& rhs) {
    return std::sqrt(squared_length(subtract(lhs, rhs)));
}

double signed_six_volume(
    const Point3d& a,
    const Point3d& b,
    const Point3d& c,
    const Point3d& d) {
    return dot(subtract(b, a), cross(subtract(c, a), subtract(d, a)));
}

double triangle_area(
    const Point3d& a,
    const Point3d& b,
    const Point3d& c) {
    return 0.5 * std::sqrt(squared_length(cross(subtract(b, a), subtract(c, a))));
}

bool circumcenter(
    const std::array<Point3d, 4>& vertices,
    Point3d& center,
    double& radius_squared) {
    double matrix[3][4]{};
    const auto norm = [](const Point3d& p) { return dot(p, p); };
    const double base = norm(vertices[0]);
    for (std::size_t row = 0; row < 3U; ++row) {
        const Point3d delta = subtract(vertices[row + 1U], vertices[0]);
        matrix[row][0] = delta.x;
        matrix[row][1] = delta.y;
        matrix[row][2] = delta.z;
        matrix[row][3] = 0.5 * (norm(vertices[row + 1U]) - base);
    }
    for (std::size_t column = 0; column < 3U; ++column) {
        std::size_t pivot = column;
        for (std::size_t row = column + 1U; row < 3U; ++row) {
            if (std::abs(matrix[row][column]) >
                std::abs(matrix[pivot][column])) {
                pivot = row;
            }
        }
        if (std::abs(matrix[pivot][column]) <= 1.0e-24) {
            return false;
        }
        if (pivot != column) {
            for (std::size_t entry = column; entry < 4U; ++entry) {
                std::swap(matrix[pivot][entry], matrix[column][entry]);
            }
        }
        const double inverse = 1.0 / matrix[column][column];
        for (std::size_t entry = column; entry < 4U; ++entry) {
            matrix[column][entry] *= inverse;
        }
        for (std::size_t row = 0; row < 3U; ++row) {
            if (row == column) {
                continue;
            }
            const double factor = matrix[row][column];
            for (std::size_t entry = column; entry < 4U; ++entry) {
                matrix[row][entry] -= factor * matrix[column][entry];
            }
        }
    }
    center = {matrix[0][3], matrix[1][3], matrix[2][3]};
    radius_squared = 0.0;
    for (const Point3d& point : vertices) {
        radius_squared = std::max(radius_squared, squared_length(subtract(center, point)));
    }
    return radius_squared > 1.0e-24 && std::isfinite(radius_squared);
}

double tet_quality(const BaseMesh& mesh, const Tetrahedron& tet) {
    std::array<Point3d, 4> p{{
        mesh.points[tet.point_ids[0]], mesh.points[tet.point_ids[1]],
        mesh.points[tet.point_ids[2]], mesh.points[tet.point_ids[3]],
    }};
    const double volume6 = std::abs(signed_six_volume(p[0], p[1], p[2], p[3]));
    if (!(volume6 > 1.0e-30)) {
        return 0.0;
    }
    const double area = triangle_area(p[0], p[1], p[2]) +
                        triangle_area(p[0], p[1], p[3]) +
                        triangle_area(p[0], p[2], p[3]) +
                        triangle_area(p[1], p[2], p[3]);
    Point3d center{};
    double radius_squared = 0.0;
    if (!(area > 0.0) || !circumcenter(p, center, radius_squared)) {
        return 0.0;
    }
    return 3.0 * (0.5 * volume6 / area) / std::sqrt(radius_squared);
}

bool make_tet(
    const BaseMesh& mesh,
    std::array<std::uint32_t, 4> ids,
    const Tetrahedron& parent,
    TetrahedronRefinementKind kind,
    Tetrahedron& result) {
    std::array<std::uint32_t, 4> unique = ids;
    std::sort(unique.begin(), unique.end());
    if (std::adjacent_find(unique.begin(), unique.end()) != unique.end()) {
        return false;
    }
    for (const std::uint32_t id : ids) {
        if (id >= mesh.points.size()) {
            return false;
        }
    }
    if (!(std::abs(signed_six_volume(
              mesh.points[ids[0]], mesh.points[ids[1]],
              mesh.points[ids[2]], mesh.points[ids[3]])) > 1.0e-30)) {
        return false;
    }
    result.point_ids = ids;
    result.refinement_level = parent.refinement_level;
    result.refinement_kind = static_cast<std::uint8_t>(kind);
    return true;
}

std::vector<std::size_t> tets_around_edge(
    const BaseMesh& mesh,
    const EdgeKey& edge) {
    std::vector<std::size_t> result;
    for (std::size_t index = 0; index < mesh.tetrahedra.size(); ++index) {
        const auto& ids = mesh.tetrahedra[index].point_ids;
        if (std::find(ids.begin(), ids.end(), edge.a) != ids.end() &&
            std::find(ids.begin(), ids.end(), edge.b) != ids.end()) {
            result.push_back(index);
        }
    }
    return result;
}

std::vector<std::size_t> tets_around_point(
    const BaseMesh& mesh,
    std::uint32_t point) {
    std::vector<std::size_t> result;
    for (std::size_t index = 0; index < mesh.tetrahedra.size(); ++index) {
        const auto& ids = mesh.tetrahedra[index].point_ids;
        if (std::find(ids.begin(), ids.end(), point) != ids.end()) {
            result.push_back(index);
        }
    }
    return result;
}

bool mesh_has_edge(
    const BaseMesh& mesh,
    std::uint32_t first,
    std::uint32_t second) {
    return first != second && !tets_around_edge(mesh, EdgeKey(first, second)).empty();
}

std::vector<std::size_t> tets_around_face(
    const BaseMesh& mesh,
    const std::array<std::uint32_t, 3>& face) {
    std::vector<std::size_t> result;
    for (std::size_t index = 0; index < mesh.tetrahedra.size(); ++index) {
        const auto& ids = mesh.tetrahedra[index].point_ids;
        bool contains = true;
        for (const std::uint32_t id : face) {
            contains = contains &&
                       std::find(ids.begin(), ids.end(), id) != ids.end();
        }
        if (contains) {
            result.push_back(index);
        }
    }
    return result;
}

void insert_split_node_in_paths(
    FeatureEdgePreservationResult* result,
    const EdgeKey& edge,
    std::uint32_t inserted) {
    if (result == nullptr) {
        return;
    }
    for (PreservedFeatureEdge& feature : result->feature_edges) {
        for (std::size_t index = 0; index + 1U < feature.mesh_path.size(); ++index) {
            if (EdgeKey(feature.mesh_path[index], feature.mesh_path[index + 1U]) == edge) {
                feature.mesh_path.insert(feature.mesh_path.begin() + index + 1U, inserted);
                ++index;
            }
        }
    }
}

bool split_edge(
    BaseMesh& mesh,
    std::vector<int>* node_types,
    FeatureEdgePreservationResult* result,
    const EdgeKey& edge,
    const Point3d& point,
    std::size_t maximum_tets,
    double minimum_quality,
    std::uint32_t& inserted) {
    const std::vector<std::size_t> ring = tets_around_edge(mesh, edge);
    if (ring.empty() || ring.size() > maximum_tets ||
        mesh.tetrahedra.size() > maximum_tets - ring.size()) {
        return false;
    }
    BaseMesh trial = mesh;
    inserted = static_cast<std::uint32_t>(trial.points.size());
    trial.points.push_back(point);
    std::vector<Tetrahedron> replacements;
    std::vector<Tetrahedron> appended;
    replacements.reserve(ring.size());
    appended.reserve(ring.size());
    for (const std::size_t tet_id : ring) {
        const Tetrahedron parent = trial.tetrahedra[tet_id];
        std::array<std::uint32_t, 2> other{};
        std::size_t count = 0;
        for (const std::uint32_t id : parent.point_ids) {
            if (id != edge.a && id != edge.b) {
                other[count++] = id;
            }
        }
        Tetrahedron first;
        Tetrahedron second;
        if (count != 2U ||
            !make_tet(trial, {{inserted, edge.a, other[0], other[1]}}, parent,
                      TetrahedronRefinementKind::feature_edge_split, first) ||
            !make_tet(trial, {{inserted, edge.b, other[0], other[1]}}, parent,
                      TetrahedronRefinementKind::feature_edge_split, second) ||
            tet_quality(trial, first) < minimum_quality ||
            tet_quality(trial, second) < minimum_quality) {
            inserted = invalid_point;
            return false;
        }
        replacements.push_back(first);
        appended.push_back(second);
    }
    for (std::size_t index = 0; index < ring.size(); ++index) {
        trial.tetrahedra[ring[index]] = replacements[index];
    }
    trial.tetrahedra.insert(trial.tetrahedra.end(), appended.begin(), appended.end());
    bool found_midpoint = false;
    for (RegisteredEdgeMidpoint& record : trial.registered_edge_midpoints) {
        if (EdgeKey(record.edge_point_ids[0], record.edge_point_ids[1]) == edge) {
            record.midpoint_id = inserted;
            found_midpoint = true;
            break;
        }
    }
    if (!found_midpoint) {
        trial.registered_edge_midpoints.push_back({{{edge.a, edge.b}}, inserted});
    }
    mesh = std::move(trial);
    if (node_types != nullptr) {
        node_types->push_back(20);
    }
    insert_split_node_in_paths(result, edge, inserted);
    return true;
}

bool split_face(
    BaseMesh& mesh,
    std::vector<int>* node_types,
    const std::array<std::uint32_t, 3>& face,
    const Point3d& point,
    std::size_t maximum_tets,
    double minimum_quality,
    std::uint32_t& inserted) {
    const std::vector<std::size_t> parents = tets_around_face(mesh, face);
    const std::size_t added = 2U * parents.size();
    if (parents.empty() || parents.size() > 2U || added > maximum_tets ||
        mesh.tetrahedra.size() > maximum_tets - added) {
        return false;
    }
    BaseMesh trial = mesh;
    inserted = static_cast<std::uint32_t>(trial.points.size());
    trial.points.push_back(point);
    std::vector<std::array<Tetrahedron, 3>> children(parents.size());
    for (std::size_t side = 0; side < parents.size(); ++side) {
        const Tetrahedron parent = trial.tetrahedra[parents[side]];
        std::uint32_t apex = invalid_point;
        for (const std::uint32_t id : parent.point_ids) {
            if (id != face[0] && id != face[1] && id != face[2]) {
                apex = id;
                break;
            }
        }
        if (apex == invalid_point) {
            inserted = invalid_point;
            return false;
        }
        for (std::size_t edge = 0; edge < 3U; ++edge) {
            if (!make_tet(
                    trial,
                    {{apex, face[edge], face[(edge + 1U) % 3U], inserted}},
                    parent, TetrahedronRefinementKind::feature_face_split,
                    children[side][edge]) ||
                tet_quality(trial, children[side][edge]) < minimum_quality) {
                inserted = invalid_point;
                return false;
            }
        }
    }
    for (std::size_t side = 0; side < parents.size(); ++side) {
        trial.tetrahedra[parents[side]] = children[side][0];
        trial.tetrahedra.push_back(children[side][1]);
        trial.tetrahedra.push_back(children[side][2]);
    }
    mesh = std::move(trial);
    if (node_types != nullptr) {
        node_types->push_back(20);
    }
    return true;
}

bool split_tetrahedron(
    BaseMesh& mesh,
    std::vector<int>* node_types,
    std::size_t tet_id,
    const Point3d& point,
    std::size_t maximum_tets,
    double minimum_quality,
    std::uint32_t& inserted) {
    if (tet_id >= mesh.tetrahedra.size() || maximum_tets < 3U ||
        mesh.tetrahedra.size() > maximum_tets - 3U) {
        return false;
    }
    BaseMesh trial = mesh;
    inserted = static_cast<std::uint32_t>(trial.points.size());
    trial.points.push_back(point);
    const Tetrahedron parent = trial.tetrahedra[tet_id];
    std::array<Tetrahedron, 4> children{};
    for (std::size_t face = 0; face < 4U; ++face) {
        const auto local = tet_faces[face];
        if (!make_tet(
                trial,
                {{inserted, parent.point_ids[local[0]], parent.point_ids[local[1]],
                  parent.point_ids[local[2]]}},
                parent, TetrahedronRefinementKind::node_face_split,
                children[face]) ||
            tet_quality(trial, children[face]) < minimum_quality) {
            inserted = invalid_point;
            return false;
        }
    }
    trial.tetrahedra[tet_id] = children[0];
    trial.tetrahedra.insert(trial.tetrahedra.end(), children.begin() + 1, children.end());
    mesh = std::move(trial);
    if (node_types != nullptr) {
        node_types->push_back(18);
    }
    return true;
}

std::array<double, 4> tet_barycentric(
    const BaseMesh& mesh,
    const Tetrahedron& tet,
    const Point3d& point) {
    const Point3d& a = mesh.points[tet.point_ids[0]];
    const Point3d& b = mesh.points[tet.point_ids[1]];
    const Point3d& c = mesh.points[tet.point_ids[2]];
    const Point3d& d = mesh.points[tet.point_ids[3]];
    const double denominator = signed_six_volume(a, b, c, d);
    if (std::abs(denominator) <= 1.0e-30) {
        return {{-2.0, -2.0, -2.0, -2.0}};
    }
    return {{
        signed_six_volume(point, b, c, d) / denominator,
        signed_six_volume(a, point, c, d) / denominator,
        signed_six_volume(a, b, point, d) / denominator,
        signed_six_volume(a, b, c, point) / denominator,
    }};
}

bool materialize_point(
    BaseMesh& mesh,
    const Point3d& point,
    std::uint32_t forbidden_existing,
    const FeatureEdgePreservationV2Options& options,
    std::uint32_t& point_id,
    FeatureNodePreservationState& state) {
    const double tolerance = options.collapsed_edge_tolerance;
    for (std::uint32_t id = 0; id < mesh.points.size(); ++id) {
        if (id != forbidden_existing && distance(mesh.points[id], point) <= tolerance) {
            point_id = id;
            state = FeatureNodePreservationState::existing_mesh_node;
            return true;
        }
    }
    constexpr double bary_tolerance = 1.0e-10;
    for (std::size_t tet_id = 0; tet_id < mesh.tetrahedra.size(); ++tet_id) {
        const Tetrahedron tet = mesh.tetrahedra[tet_id];
        const std::array<double, 4> bary = tet_barycentric(mesh, tet, point);
        bool inside = true;
        std::vector<std::size_t> zeros;
        std::vector<std::size_t> nonzeros;
        for (std::size_t local = 0; local < 4U; ++local) {
            inside = inside && bary[local] >= -bary_tolerance &&
                     bary[local] <= 1.0 + bary_tolerance;
            if (std::abs(bary[local]) <= bary_tolerance) {
                zeros.push_back(local);
            } else {
                nonzeros.push_back(local);
            }
        }
        if (!inside) {
            continue;
        }
        if (zeros.size() >= 3U) {
            std::uint32_t nearest = invalid_point;
            double best = std::numeric_limits<double>::max();
            for (const std::uint32_t id : tet.point_ids) {
                if (id == forbidden_existing) {
                    continue;
                }
                const double candidate = distance(mesh.points[id], point);
                if (candidate < best) {
                    nearest = id;
                    best = candidate;
                }
            }
            if (nearest != invalid_point && best <= tolerance) {
                point_id = nearest;
                state = FeatureNodePreservationState::existing_mesh_node;
                return true;
            }
            return false;
        }
        if (zeros.size() == 2U && nonzeros.size() == 2U) {
            if (split_edge(mesh, nullptr, nullptr,
                           EdgeKey(tet.point_ids[nonzeros[0]], tet.point_ids[nonzeros[1]]),
                           point, options.primary.maximum_tetrahedron_count,
                           options.minimum_fallback_quality, point_id)) {
                state = FeatureNodePreservationState::inserted_by_edge_split;
                return true;
            }
            return false;
        }
        if (zeros.size() == 1U) {
            const auto local_face = tet_faces[zeros[0]];
            const std::array<std::uint32_t, 3> face{{
                tet.point_ids[local_face[0]], tet.point_ids[local_face[1]],
                tet.point_ids[local_face[2]],
            }};
            if (split_face(mesh, nullptr, face, point,
                           options.primary.maximum_tetrahedron_count,
                           options.minimum_fallback_quality, point_id)) {
                state = FeatureNodePreservationState::inserted_by_face_split;
                return true;
            }
            return false;
        }
        if (split_tetrahedron(mesh, nullptr, tet_id, point,
                              options.primary.maximum_tetrahedron_count,
                              options.minimum_fallback_quality, point_id)) {
            state = FeatureNodePreservationState::inserted_by_face_split;
            return true;
        }
        return false;
    }
    return false;
}

double point_segment_parameter(
    const Point3d& point,
    const Point3d& start,
    const Point3d& end,
    double& deviation) {
    const Point3d direction = subtract(end, start);
    const double denominator = squared_length(direction);
    if (!(denominator > 0.0)) {
        deviation = distance(point, start);
        return 0.0;
    }
    const double parameter = dot(subtract(point, start), direction) / denominator;
    const Point3d projection = add(start, multiply(direction, parameter));
    deviation = distance(point, projection);
    return parameter;
}

bool find_line_path(
    const BaseMesh& mesh,
    std::uint32_t start_id,
    std::uint32_t end_id,
    const Point3d& line_start,
    const Point3d& line_end,
    double tolerance,
    std::vector<std::uint32_t>& path) {
    path.clear();
    if (start_id >= mesh.points.size() || end_id >= mesh.points.size() ||
        start_id == end_id) {
        return false;
    }
    std::vector<double> parameters(mesh.points.size(), -2.0);
    std::vector<bool> eligible(mesh.points.size(), false);
    for (std::uint32_t id = 0; id < mesh.points.size(); ++id) {
        double deviation = 0.0;
        const double parameter = point_segment_parameter(
            mesh.points[id], line_start, line_end, deviation);
        if ((deviation <= tolerance && parameter >= -1.0e-10 &&
             parameter <= 1.0 + 1.0e-10) ||
            id == start_id || id == end_id) {
            eligible[id] = true;
            parameters[id] = parameter;
        }
    }
    std::vector<std::vector<std::uint32_t>> adjacency(mesh.points.size());
    std::unordered_set<EdgeKey, EdgeHash> emitted;
    for (const Tetrahedron& tet : mesh.tetrahedra) {
        for (const auto& local : tet_edges) {
            const std::uint32_t first = tet.point_ids[local[0]];
            const std::uint32_t second = tet.point_ids[local[1]];
            const EdgeKey key(first, second);
            if (!emitted.insert(key).second || !eligible[first] || !eligible[second]) {
                continue;
            }
            adjacency[first].push_back(second);
            adjacency[second].push_back(first);
        }
    }
    std::queue<std::uint32_t> pending;
    std::vector<std::uint32_t> previous(mesh.points.size(), invalid_point);
    pending.push(start_id);
    previous[start_id] = start_id;
    while (!pending.empty() && previous[end_id] == invalid_point) {
        const std::uint32_t current = pending.front();
        pending.pop();
        std::sort(adjacency[current].begin(), adjacency[current].end(),
                  [&](std::uint32_t lhs, std::uint32_t rhs) {
                      return parameters[lhs] < parameters[rhs];
                  });
        for (const std::uint32_t next : adjacency[current]) {
            if (previous[next] != invalid_point ||
                parameters[next] + 1.0e-12 < parameters[current]) {
                continue;
            }
            previous[next] = current;
            pending.push(next);
        }
    }
    if (previous[end_id] == invalid_point) {
        return false;
    }
    for (std::uint32_t current = end_id;; current = previous[current]) {
        path.push_back(current);
        if (current == start_id) {
            break;
        }
    }
    std::reverse(path.begin(), path.end());
    return path.size() >= 2U;
}

bool path_is_valid(
    const BaseMesh& mesh,
    const PreservedFeatureEdge& record,
    const FeatureEdge& feature,
    const FacetMesh& facets,
    double tolerance,
    bool allow_collapsed,
    double collapse_tolerance) {
    if (feature.point_ids[0] >= facets.points.size() ||
        feature.point_ids[1] >= facets.points.size() || record.mesh_path.empty()) {
        return false;
    }
    const Point3d& start = facets.points[feature.point_ids[0]];
    const Point3d& end = facets.points[feature.point_ids[1]];
    if (record.mesh_path.size() == 1U) {
        const std::uint32_t id = record.mesh_path.front();
        return id < mesh.points.size() && allow_collapsed &&
               distance(start, end) <= collapse_tolerance &&
               distance(mesh.points[id], start) <= tolerance &&
               distance(mesh.points[id], end) <= tolerance;
    }
    if (record.mesh_path.front() >= mesh.points.size() ||
        record.mesh_path.back() >= mesh.points.size()) {
        return false;
    }
    const bool forward_endpoints =
        distance(mesh.points[record.mesh_path.front()], start) <= tolerance &&
        distance(mesh.points[record.mesh_path.back()], end) <= tolerance;
    const bool reverse_endpoints =
        distance(mesh.points[record.mesh_path.front()], end) <= tolerance &&
        distance(mesh.points[record.mesh_path.back()], start) <= tolerance;
    if (!forward_endpoints && !reverse_endpoints) {
        return false;
    }
    double first_deviation = 0.0;
    double last_deviation = 0.0;
    const double first_parameter = point_segment_parameter(
        mesh.points[record.mesh_path.front()], start, end, first_deviation);
    const double final_parameter = point_segment_parameter(
        mesh.points[record.mesh_path.back()], start, end, last_deviation);
    const bool increasing = first_parameter <= final_parameter;
    double last_parameter = first_parameter;
    for (std::size_t index = 0; index < record.mesh_path.size(); ++index) {
        const std::uint32_t id = record.mesh_path[index];
        if (id >= mesh.points.size()) {
            return false;
        }
        double deviation = 0.0;
        const double parameter = point_segment_parameter(mesh.points[id], start, end, deviation);
        const bool wrong_direction = increasing
            ? parameter + 1.0e-10 < last_parameter
            : parameter - 1.0e-10 > last_parameter;
        if (deviation > tolerance || wrong_direction) {
            return false;
        }
        last_parameter = parameter;
        if (index + 1U < record.mesh_path.size() &&
            !mesh_has_edge(mesh, id, record.mesh_path[index + 1U])) {
            return false;
        }
    }
    return true;
}

bool closest_segments(
    const Point3d& p0,
    const Point3d& p1,
    const Point3d& q0,
    const Point3d& q1,
    double& s,
    double& t,
    Point3d& on_p,
    Point3d& on_q) {
    const Point3d d1 = subtract(p1, p0);
    const Point3d d2 = subtract(q1, q0);
    const Point3d r = subtract(p0, q0);
    const double a = dot(d1, d1);
    const double e = dot(d2, d2);
    const double f = dot(d2, r);
    if (a <= 1.0e-30 || e <= 1.0e-30) {
        return false;
    }
    const double b = dot(d1, d2);
    const double c = dot(d1, r);
    const double denominator = a * e - b * b;
    s = denominator > 1.0e-30 ? (b * f - c * e) / denominator : 0.0;
    s = std::max(0.0, std::min(1.0, s));
    t = (b * s + f) / e;
    if (t < 0.0) {
        t = 0.0;
        s = std::max(0.0, std::min(1.0, -c / a));
    } else if (t > 1.0) {
        t = 1.0;
        s = std::max(0.0, std::min(1.0, (b - c) / a));
    }
    on_p = add(p0, multiply(d1, s));
    on_q = add(q0, multiply(d2, t));
    return true;
}

bool find_next_crossing(
    const BaseMesh& mesh,
    std::uint32_t current,
    const Point3d& line_start,
    const Point3d& line_end,
    double tolerance,
    Crossing& best) {
    double current_deviation = 0.0;
    const double current_parameter = point_segment_parameter(
        mesh.points[current], line_start, line_end, current_deviation);
    const Point3d direction = subtract(line_end, line_start);
    const double line_length = std::sqrt(squared_length(direction));
    const double parameter_epsilon =
        std::max(1.0e-12, tolerance / std::max(line_length, tolerance));
    bool found = false;
    best.parameter = std::numeric_limits<double>::max();
    for (const std::size_t tet_id : tets_around_point(mesh, current)) {
        const Tetrahedron& tet = mesh.tetrahedra[tet_id];
        std::size_t current_local = 4U;
        for (std::size_t local = 0; local < 4U; ++local) {
            if (tet.point_ids[local] == current) {
                current_local = local;
                break;
            }
        }
        if (current_local >= 4U) {
            continue;
        }
        const auto local = tet_faces[current_local];
        const std::array<std::uint32_t, 3> face{{
            tet.point_ids[local[0]], tet.point_ids[local[1]],
            tet.point_ids[local[2]],
        }};
        const Point3d& a = mesh.points[face[0]];
        const Point3d& b = mesh.points[face[1]];
        const Point3d& c = mesh.points[face[2]];
        const Point3d normal = cross(subtract(b, a), subtract(c, a));
        const double denominator = dot(normal, direction);
        if (std::abs(denominator) <= 1.0e-18 *
                std::max(1.0, std::sqrt(squared_length(normal)) * line_length)) {
            if (std::abs(dot(normal, subtract(line_start, a))) >
                tolerance * std::max(1.0, std::sqrt(squared_length(normal)))) {
                continue;
            }
            for (std::size_t edge_index = 0; edge_index < 3U; ++edge_index) {
                const EdgeKey edge(face[edge_index], face[(edge_index + 1U) % 3U]);
                double s = 0.0;
                double t = 0.0;
                Point3d on_line{};
                Point3d on_edge{};
                if (!closest_segments(line_start, line_end, mesh.points[edge.a],
                                      mesh.points[edge.b], s, t, on_line, on_edge) ||
                    distance(on_line, on_edge) > tolerance ||
                    s <= current_parameter + parameter_epsilon ||
                    s >= best.parameter || s > 1.0 + parameter_epsilon) {
                    continue;
                }
                best.face = face;
                best.point = multiply(add(on_line, on_edge), 0.5);
                best.parameter = s;
                best.coplanar_edge_hit = true;
                best.coplanar_edge = edge;
                found = true;
            }
            continue;
        }
        const double parameter = dot(normal, subtract(a, line_start)) / denominator;
        if (parameter <= current_parameter + parameter_epsilon ||
            parameter >= best.parameter || parameter > 1.0 + parameter_epsilon) {
            continue;
        }
        const Point3d hit = add(line_start, multiply(direction, parameter));
        const Point3d v0 = subtract(b, a);
        const Point3d v1 = subtract(c, a);
        const Point3d v2 = subtract(hit, a);
        const double d00 = dot(v0, v0);
        const double d01 = dot(v0, v1);
        const double d11 = dot(v1, v1);
        const double d20 = dot(v2, v0);
        const double d21 = dot(v2, v1);
        const double bary_denominator = d00 * d11 - d01 * d01;
        if (std::abs(bary_denominator) <= 1.0e-30) {
            continue;
        }
        const double beta = (d11 * d20 - d01 * d21) / bary_denominator;
        const double gamma = (d00 * d21 - d01 * d20) / bary_denominator;
        const double alpha = 1.0 - beta - gamma;
        const double bary_tolerance =
            std::max(1.0e-10, tolerance / std::max({distance(a, b), distance(a, c), distance(b, c), tolerance}));
        if (alpha < -bary_tolerance || beta < -bary_tolerance ||
            gamma < -bary_tolerance) {
            continue;
        }
        best.face = face;
        best.point = hit;
        best.parameter = parameter;
        best.barycentric = {{alpha, beta, gamma}};
        best.coplanar_edge_hit = false;
        found = true;
    }
    return found;
}

bool advance_crossing(
    FeatureEdgePreservationResult& result,
    const Crossing& crossing,
    const FeatureEdgePreservationV2Options& options,
    std::uint32_t& next) {
    const double tolerance = std::max(
        options.primary.global_tolerance, options.primary.mesh_tolerance);
    for (const std::uint32_t vertex : crossing.face) {
        if (distance(result.mesh.points[vertex], crossing.point) <= tolerance) {
            next = vertex;
            return true;
        }
    }
    EdgeKey split_candidate;
    bool split_on_edge = crossing.coplanar_edge_hit;
    if (split_on_edge) {
        split_candidate = crossing.coplanar_edge;
    } else {
        constexpr double bary_tolerance = 1.0e-9;
        for (std::size_t index = 0; index < 3U; ++index) {
            if (crossing.barycentric[index] <= bary_tolerance) {
                split_candidate = EdgeKey(
                    crossing.face[(index + 1U) % 3U],
                    crossing.face[(index + 2U) % 3U]);
                split_on_edge = true;
                break;
            }
        }
    }
    if (split_on_edge) {
        if (!split_edge(result.mesh, &result.node_types, &result,
                        split_candidate, crossing.point,
                        options.primary.maximum_tetrahedron_count,
                        options.minimum_fallback_quality, next)) {
            return false;
        }
        ++result.edge_split_count;
        ++result.forced_edge_split_count;
        return true;
    }
    if (!split_face(result.mesh, &result.node_types, crossing.face,
                    crossing.point, options.primary.maximum_tetrahedron_count,
                    options.minimum_fallback_quality, next)) {
        return false;
    }
    ++result.face_split_count;
    ++result.forced_face_split_count;
    return true;
}

bool recover_by_robust_walk(
    FeatureEdgePreservationResult& result,
    std::uint32_t start_id,
    std::uint32_t end_id,
    const Point3d& line_start,
    const Point3d& line_end,
    const FeatureEdgePreservationV2Options& options,
    std::vector<std::uint32_t>& path) {
    const double tolerance = std::max(
        options.primary.mesh_tolerance, options.primary.preserve_tolerance);
    if (find_line_path(result.mesh, start_id, end_id, line_start, line_end,
                       tolerance, path)) {
        return true;
    }
    std::uint32_t current = start_id;
    path = {current};
    std::unordered_set<std::uint32_t> visited;
    visited.insert(current);
    for (std::size_t step = 0; step < options.primary.maximum_path_steps; ++step) {
        if (mesh_has_edge(result.mesh, current, end_id)) {
            path.push_back(end_id);
            return true;
        }
        Crossing crossing;
        if (!find_next_crossing(result.mesh, current, line_start, line_end,
                                tolerance, crossing)) {
            return false;
        }
        std::uint32_t next = invalid_point;
        if (!advance_crossing(result, crossing, options, next) ||
            next == invalid_point || next == current ||
            !visited.insert(next).second ||
            !mesh_has_edge(result.mesh, current, next)) {
            return false;
        }
        path.push_back(next);
        current = next;
    }
    return false;
}

bool try_direct_two_to_three_swap(
    FeatureEdgePreservationResult& result,
    std::uint32_t start,
    std::uint32_t target,
    const FeatureEdgePreservationV2Options& options) {
    std::unordered_map<FaceKey, std::vector<std::size_t>, FaceHash> faces;
    faces.reserve(result.mesh.tetrahedra.size() * 2U);
    for (std::size_t tet_id = 0; tet_id < result.mesh.tetrahedra.size(); ++tet_id) {
        const Tetrahedron& tet = result.mesh.tetrahedra[tet_id];
        for (const auto& local : tet_faces) {
            faces[FaceKey({{tet.point_ids[local[0]], tet.point_ids[local[1]],
                           tet.point_ids[local[2]]}})].push_back(tet_id);
        }
    }
    for (const auto& item : faces) {
        if (item.second.size() != 2U) {
            continue;
        }
        const std::array<std::uint32_t, 3>& face = item.first.ids;
        std::array<std::uint32_t, 2> apex{{invalid_point, invalid_point}};
        for (std::size_t side = 0; side < 2U; ++side) {
            for (const std::uint32_t id : result.mesh.tetrahedra[item.second[side]].point_ids) {
                if (std::find(face.begin(), face.end(), id) == face.end()) {
                    apex[side] = id;
                    break;
                }
            }
        }
        if (!((apex[0] == start && apex[1] == target) ||
              (apex[0] == target && apex[1] == start))) {
            continue;
        }
        const double side0 = signed_six_volume(
            result.mesh.points[face[0]], result.mesh.points[face[1]],
            result.mesh.points[face[2]], result.mesh.points[apex[0]]);
        const double side1 = signed_six_volume(
            result.mesh.points[face[0]], result.mesh.points[face[1]],
            result.mesh.points[face[2]], result.mesh.points[apex[1]]);
        const Point3d direction = subtract(
            result.mesh.points[apex[1]], result.mesh.points[apex[0]]);
        const Point3d normal = cross(
            subtract(result.mesh.points[face[1]], result.mesh.points[face[0]]),
            subtract(result.mesh.points[face[2]], result.mesh.points[face[0]]));
        const double denominator = dot(normal, direction);
        if (!(side0 * side1 < 0.0) || std::abs(denominator) <= 1.0e-30 ||
            result.mesh.tetrahedra.size() >= options.primary.maximum_tetrahedron_count) {
            continue;
        }
        const double parameter = dot(
            normal, subtract(result.mesh.points[face[0]],
                             result.mesh.points[apex[0]])) / denominator;
        const Point3d hit = add(
            result.mesh.points[apex[0]], multiply(direction, parameter));
        const Point3d v0 = subtract(result.mesh.points[face[1]], result.mesh.points[face[0]]);
        const Point3d v1 = subtract(result.mesh.points[face[2]], result.mesh.points[face[0]]);
        const Point3d v2 = subtract(hit, result.mesh.points[face[0]]);
        const double d00 = dot(v0, v0);
        const double d01 = dot(v0, v1);
        const double d11 = dot(v1, v1);
        const double d20 = dot(v2, v0);
        const double d21 = dot(v2, v1);
        const double bary_denominator = d00 * d11 - d01 * d01;
        if (parameter <= 0.0 || parameter >= 1.0 ||
            std::abs(bary_denominator) <= 1.0e-30) {
            continue;
        }
        const double beta = (d11 * d20 - d01 * d21) / bary_denominator;
        const double gamma = (d00 * d21 - d01 * d20) / bary_denominator;
        const double alpha = 1.0 - beta - gamma;
        if (alpha < -1.0e-10 || beta < -1.0e-10 || gamma < -1.0e-10) {
            continue;
        }
        BaseMesh trial = result.mesh;
        const Tetrahedron parent = trial.tetrahedra[item.second[0]];
        std::array<Tetrahedron, 3> children{};
        bool valid = true;
        for (std::size_t edge = 0; edge < 3U; ++edge) {
            valid = valid && make_tet(
                trial,
                {{start, target, face[edge], face[(edge + 1U) % 3U]}},
                parent, TetrahedronRefinementKind::feature_edge_swap,
                children[edge]);
            valid = valid &&
                    tet_quality(trial, children[edge]) >= options.minimum_fallback_quality;
        }
        if (!valid) {
            continue;
        }
        trial.tetrahedra[item.second[0]] = children[0];
        trial.tetrahedra[item.second[1]] = children[1];
        trial.tetrahedra.push_back(children[2]);
        result.mesh = std::move(trial);
        ++result.edge_swap_count;
        return true;
    }
    return false;
}

const PreservedFeatureNode* find_feature_node(
    const NodePreservationResult& nodes,
    std::uint32_t facet_point);

struct EdgeCut {
    std::size_t feature_index = 0;
    double edge_parameter = 0.0;
    Point3d point{};
};

bool reduce_one_multi_cut_edge(
    FeatureEdgePreservationResult& result,
    const NodePreservationResult& nodes,
    const FacetMesh& facets,
    const FeatureTopology& features,
    const FeatureEdgePreservationV2Options& options) {
    std::unordered_set<EdgeKey, EdgeHash> mesh_edges;
    mesh_edges.reserve(result.mesh.tetrahedra.size() * 3U);
    for (const Tetrahedron& tet : result.mesh.tetrahedra) {
        for (const auto& local : tet_edges) {
            mesh_edges.insert(EdgeKey(
                tet.point_ids[local[0]], tet.point_ids[local[1]]));
        }
    }
    std::unordered_map<EdgeKey, std::vector<EdgeCut>, EdgeHash> cuts;
    const double tolerance = std::max(
        options.primary.mesh_tolerance, options.primary.preserve_tolerance);
    for (const PreservedFeatureEdge& record : result.feature_edges) {
        if (record.state != FeatureEdgePreservationState::unresolved ||
            record.source_feature_index >= features.feature_edges.size()) {
            continue;
        }
        const FeatureEdge& feature =
            features.feature_edges[record.source_feature_index];
        if (feature.point_ids[0] >= facets.points.size() ||
            feature.point_ids[1] >= facets.points.size()) {
            continue;
        }
        const PreservedFeatureNode* first =
            find_feature_node(nodes, feature.point_ids[0]);
        const PreservedFeatureNode* second =
            find_feature_node(nodes, feature.point_ids[1]);
        if (first == nullptr || second == nullptr) {
            continue;
        }
        const Point3d& line_start = facets.points[feature.point_ids[0]];
        const Point3d& line_end = facets.points[feature.point_ids[1]];
        for (const EdgeKey& edge : mesh_edges) {
            if (edge.a == first->mesh_point_id || edge.a == second->mesh_point_id ||
                edge.b == first->mesh_point_id || edge.b == second->mesh_point_id) {
                continue;
            }
            double line_parameter = 0.0;
            double edge_parameter = 0.0;
            Point3d on_line{};
            Point3d on_edge{};
            if (!closest_segments(
                    line_start, line_end, result.mesh.points[edge.a],
                    result.mesh.points[edge.b], line_parameter, edge_parameter,
                    on_line, on_edge) ||
                distance(on_line, on_edge) > tolerance ||
                line_parameter <= 1.0e-9 || line_parameter >= 1.0 - 1.0e-9 ||
                edge_parameter <= 1.0e-9 || edge_parameter >= 1.0 - 1.0e-9) {
                continue;
            }
            cuts[edge].push_back({
                record.source_feature_index, edge_parameter, on_edge});
        }
    }
    const EdgeKey* selected_edge = nullptr;
    const EdgeCut* selected_cut = nullptr;
    std::size_t selected_feature_count = 1U;
    for (const auto& item : cuts) {
        std::unordered_set<std::size_t> unique_features;
        for (const EdgeCut& cut : item.second) {
            unique_features.insert(cut.feature_index);
        }
        if (unique_features.size() < 2U ||
            unique_features.size() < selected_feature_count) {
            continue;
        }
        selected_feature_count = unique_features.size();
        selected_edge = &item.first;
        selected_cut = &*std::min_element(
            item.second.begin(), item.second.end(),
            [](const EdgeCut& lhs, const EdgeCut& rhs) {
                return std::abs(lhs.edge_parameter - 0.5) <
                       std::abs(rhs.edge_parameter - 0.5);
            });
    }
    if (selected_edge == nullptr || selected_cut == nullptr) {
        return false;
    }
    std::uint32_t inserted = invalid_point;
    if (!split_edge(
            result.mesh, &result.node_types, &result, *selected_edge,
            selected_cut->point, options.primary.maximum_tetrahedron_count,
            options.minimum_fallback_quality, inserted)) {
        return false;
    }
    ++result.edge_split_count;
    ++result.forced_edge_split_count;
    return true;
}

PreservedFeatureNode* find_feature_node(
    NodePreservationResult& nodes,
    std::uint32_t facet_point) {
    for (PreservedFeatureNode& node : nodes.feature_nodes) {
        if (node.facet_point_id == facet_point) {
            return &node;
        }
    }
    return nullptr;
}

const PreservedFeatureNode* find_feature_node(
    const NodePreservationResult& nodes,
    std::uint32_t facet_point) {
    for (const PreservedFeatureNode& node : nodes.feature_nodes) {
        if (node.facet_point_id == facet_point) {
            return &node;
        }
    }
    return nullptr;
}

PreservedFeatureEdge* find_record(
    FeatureEdgePreservationResult& result,
    std::size_t source_index) {
    for (PreservedFeatureEdge& edge : result.feature_edges) {
        if (edge.source_feature_index == source_index) {
            return &edge;
        }
    }
    return nullptr;
}

void recompute_summary(FeatureEdgePreservationResult& result) {
    result.early_preserved_count = 0;
    result.recovered_count = 0;
    result.unresolved_count = 0;
    result.preserved_subedge_count = 0;
    for (const PreservedFeatureEdge& edge : result.feature_edges) {
        if (edge.state == FeatureEdgePreservationState::early_preserved) {
            ++result.early_preserved_count;
        } else if (edge.state == FeatureEdgePreservationState::recovered) {
            ++result.recovered_count;
        } else {
            ++result.unresolved_count;
        }
        if (edge.state != FeatureEdgePreservationState::unresolved &&
            edge.mesh_path.size() >= 2U) {
            result.preserved_subedge_count += edge.mesh_path.size() - 1U;
        }
    }
    result.complete = result.unresolved_count == 0U;
}

bool validate_mesh(const BaseMesh& mesh, std::string& error) {
    std::unordered_map<FaceKey, std::uint8_t, FaceHash> faces;
    faces.reserve(mesh.tetrahedra.size() * 2U);
    for (const Tetrahedron& tet : mesh.tetrahedra) {
        std::array<std::uint32_t, 4> unique = tet.point_ids;
        std::sort(unique.begin(), unique.end());
        if (std::adjacent_find(unique.begin(), unique.end()) != unique.end()) {
            error = "V2 produced a tetrahedron with duplicate vertices.";
            return false;
        }
        for (const std::uint32_t id : tet.point_ids) {
            if (id >= mesh.points.size()) {
                error = "V2 produced a tetrahedron with an invalid point index.";
                return false;
            }
        }
        if (!(std::abs(signed_six_volume(
                  mesh.points[tet.point_ids[0]], mesh.points[tet.point_ids[1]],
                  mesh.points[tet.point_ids[2]], mesh.points[tet.point_ids[3]])) >
              1.0e-30)) {
            error = "V2 produced a zero-volume tetrahedron.";
            return false;
        }
        for (const auto& local : tet_faces) {
            std::uint8_t& incidence = faces[FaceKey({{
                tet.point_ids[local[0]], tet.point_ids[local[1]],
                tet.point_ids[local[2]],
            }})];
            ++incidence;
            if (incidence > 2U) {
                error = "V2 produced a non-manifold tetrahedron face.";
                return false;
            }
        }
    }
    return true;
}

bool valid_v2_options(const FeatureEdgePreservationV2Options& options) {
    return options.maximum_global_passes > 0U &&
           options.minimum_fallback_quality > 0.0 &&
           std::isfinite(options.minimum_fallback_quality) &&
           options.collapsed_edge_tolerance > 0.0 &&
           std::isfinite(options.collapsed_edge_tolerance);
}

}  // namespace

bool preserve_feature_edges_v2(
    const NodePreservationResult& node_result,
    const FacetMesh& facet_mesh,
    const FeatureTopology& features,
    const FeatureEdgePreservationV2Options& options,
    FeatureEdgePreservationResult& output,
    std::string& error) {
    error.clear();
    output = FeatureEdgePreservationResult{};
    if (!valid_v2_options(options)) {
        error = "FeatureEdgePreservationV2Options contains an invalid limit, tolerance, or quality.";
        return false;
    }

    NodePreservationResult repaired = node_result;
    std::unordered_set<std::size_t> noncollapsible_same_node;
    std::size_t endpoint_insertions = 0;
    for (std::size_t feature_index = 0;
         feature_index < features.feature_edges.size(); ++feature_index) {
        const FeatureEdge& feature = features.feature_edges[feature_index];
        if (feature.point_ids[0] >= facet_mesh.points.size() ||
            feature.point_ids[1] >= facet_mesh.points.size()) {
            noncollapsible_same_node.insert(feature_index);
            continue;
        }
        PreservedFeatureNode* first = find_feature_node(repaired, feature.point_ids[0]);
        PreservedFeatureNode* second = find_feature_node(repaired, feature.point_ids[1]);
        if (first == nullptr || second == nullptr ||
            first->mesh_point_id == invalid_point ||
            second->mesh_point_id == invalid_point ||
            first->mesh_point_id != second->mesh_point_id) {
            continue;
        }
        const double source_length = distance(
            facet_mesh.points[feature.point_ids[0]],
            facet_mesh.points[feature.point_ids[1]]);
        if (options.allow_collapsed_feature_edges &&
            source_length <= options.collapsed_edge_tolerance) {
            continue;
        }
        if (first->mesh_point_id >= repaired.mesh.points.size()) {
            noncollapsible_same_node.insert(feature_index);
            continue;
        }
        const Point3d& bound = repaired.mesh.points[first->mesh_point_id];
        const double first_error = distance(bound, facet_mesh.points[feature.point_ids[0]]);
        const double second_error = distance(bound, facet_mesh.points[feature.point_ids[1]]);
        PreservedFeatureNode* materialized =
            first_error >= second_error ? first : second;
        const Point3d target = facet_mesh.points[materialized->facet_point_id];
        std::uint32_t inserted = invalid_point;
        FeatureNodePreservationState state = FeatureNodePreservationState::unresolved;
        if (materialize_point(
                repaired.mesh, target, first->mesh_point_id, options,
                inserted, state)) {
            materialized->mesh_point_id = inserted;
            materialized->state = state;
            ++endpoint_insertions;
        } else {
            noncollapsible_same_node.insert(feature_index);
        }
    }

    if (!preserve_feature_edges(
            repaired, facet_mesh, features, options.primary, output, error)) {
        return false;
    }
    output.endpoint_insertion_count = endpoint_insertions;
    if (output.node_types.size() < output.mesh.points.size()) {
        output.node_types.resize(output.mesh.points.size(), 0);
    }

    const double path_tolerance = std::max(
        options.primary.mesh_tolerance, options.primary.preserve_tolerance);
    for (PreservedFeatureEdge& record : output.feature_edges) {
        if (record.source_feature_index >= features.feature_edges.size() ||
            noncollapsible_same_node.count(record.source_feature_index) != 0U ||
            !path_is_valid(
                output.mesh, record,
                features.feature_edges[record.source_feature_index], facet_mesh,
                path_tolerance, options.allow_collapsed_feature_edges,
                options.collapsed_edge_tolerance)) {
            record.state = FeatureEdgePreservationState::unresolved;
            record.mesh_path.clear();
        }
    }
    recompute_summary(output);

    for (std::size_t pass = 0;
         pass < options.maximum_global_passes && output.unresolved_count != 0U;
         ++pass) {
        ++output.global_recovery_pass_count;
        bool pass_progress = false;

        // Refresh paths after every topology change.  The BFS is deliberately
        // non-greedy, so branching collinear paths cannot hide a valid route.
        for (std::size_t feature_index = 0;
             feature_index < features.feature_edges.size(); ++feature_index) {
            PreservedFeatureEdge* record = find_record(output, feature_index);
            if (record == nullptr ||
                record->state != FeatureEdgePreservationState::unresolved) {
                continue;
            }
            const FeatureEdge& feature = features.feature_edges[feature_index];
            const PreservedFeatureNode* first = find_feature_node(repaired, feature.point_ids[0]);
            const PreservedFeatureNode* second = find_feature_node(repaired, feature.point_ids[1]);
            if (first == nullptr || second == nullptr ||
                first->mesh_point_id == second->mesh_point_id ||
                first->mesh_point_id >= output.mesh.points.size() ||
                second->mesh_point_id >= output.mesh.points.size()) {
                continue;
            }
            std::vector<std::uint32_t> path;
            if (find_line_path(
                    output.mesh, first->mesh_point_id, second->mesh_point_id,
                    facet_mesh.points[feature.point_ids[0]],
                    facet_mesh.points[feature.point_ids[1]],
                    path_tolerance, path)) {
                record->state = FeatureEdgePreservationState::recovered;
                record->mesh_path = std::move(path);
                pass_progress = true;
            }
        }
        recompute_summary(output);
        if (output.unresolved_count == 0U) {
            break;
        }

        // The reference implementation explicitly reduces mesh edges cut by
        // several outstanding constraints.  Split one highest-conflict edge
        // per pass, then let the refresh/walk stages consume the new vertex.
        if (options.enable_multi_cut_reduction) {
            FeatureEdgePreservationResult multi_cut_trial = output;
            if (reduce_one_multi_cut_edge(
                    multi_cut_trial, repaired, facet_mesh, features, options)) {
                output = std::move(multi_cut_trial);
                pass_progress = true;
            }
        }

        for (std::size_t feature_index = 0;
             feature_index < features.feature_edges.size(); ++feature_index) {
            PreservedFeatureEdge* current_record = find_record(output, feature_index);
            if (current_record == nullptr ||
                current_record->state != FeatureEdgePreservationState::unresolved) {
                continue;
            }
            const FeatureEdge& feature = features.feature_edges[feature_index];
            const PreservedFeatureNode* first = find_feature_node(repaired, feature.point_ids[0]);
            const PreservedFeatureNode* second = find_feature_node(repaired, feature.point_ids[1]);
            if (first == nullptr || second == nullptr ||
                first->mesh_point_id == second->mesh_point_id ||
                first->mesh_point_id >= output.mesh.points.size() ||
                second->mesh_point_id >= output.mesh.points.size()) {
                continue;
            }

            FeatureEdgePreservationResult trial = output;
            bool recovered = false;
            if (options.enable_edge_swaps &&
                try_direct_two_to_three_swap(
                    trial, first->mesh_point_id, second->mesh_point_id, options)) {
                recovered = true;
            }
            std::vector<std::uint32_t> path;
            if (!recovered && options.enable_forced_splits) {
                recovered = recover_by_robust_walk(
                    trial, first->mesh_point_id, second->mesh_point_id,
                    facet_mesh.points[feature.point_ids[0]],
                    facet_mesh.points[feature.point_ids[1]], options, path);
                if (!recovered) {
                    FeatureEdgePreservationResult reverse_trial = output;
                    std::vector<std::uint32_t> reverse_path;
                    recovered = recover_by_robust_walk(
                        reverse_trial, second->mesh_point_id, first->mesh_point_id,
                        facet_mesh.points[feature.point_ids[1]],
                        facet_mesh.points[feature.point_ids[0]], options,
                        reverse_path);
                    if (recovered) {
                        trial = std::move(reverse_trial);
                        std::reverse(reverse_path.begin(), reverse_path.end());
                        path = std::move(reverse_path);
                    }
                }
            }
            if (recovered) {
                if (path.empty() && !find_line_path(
                        trial.mesh, first->mesh_point_id, second->mesh_point_id,
                        facet_mesh.points[feature.point_ids[0]],
                        facet_mesh.points[feature.point_ids[1]],
                        path_tolerance, path)) {
                    recovered = false;
                }
            }
            if (recovered) {
                PreservedFeatureEdge* trial_record = find_record(trial, feature_index);
                if (trial_record != nullptr) {
                    trial_record->state = FeatureEdgePreservationState::recovered;
                    trial_record->mesh_path = std::move(path);
                    output = std::move(trial);
                    pass_progress = true;
                }
            } else {
                ++output.rollback_count;
            }
        }
        recompute_summary(output);
        if (!pass_progress) {
            break;
        }
    }

    // Final audit is independent of the recovery status flags.
    for (PreservedFeatureEdge& record : output.feature_edges) {
        if (record.source_feature_index >= features.feature_edges.size() ||
            !path_is_valid(
                output.mesh, record,
                features.feature_edges[record.source_feature_index], facet_mesh,
                path_tolerance, options.allow_collapsed_feature_edges,
                options.collapsed_edge_tolerance)) {
            record.state = FeatureEdgePreservationState::unresolved;
            record.mesh_path.clear();
        }
    }
    recompute_summary(output);
    if (!validate_mesh(output.mesh, error)) {
        return false;
    }
    if (options.require_complete && !output.complete) {
        std::ostringstream message;
        message << "FeatureEdge preservation V2 left " << output.unresolved_count
                << " of " << output.feature_edges.size()
                << " edges unresolved after "
                << output.global_recovery_pass_count << " global passes.";
        error = message.str();
        return false;
    }
    return true;
}

}  // namespace geometry
