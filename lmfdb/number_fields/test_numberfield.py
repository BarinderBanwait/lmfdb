import os
import tempfile
from unittest.mock import patch

from lmfdb.tests import LmfdbTest

class NumberFieldTest(LmfdbTest):
    # All tests should pass
    def test_Q(self):
        self.check_args('/NumberField/Q', r'\chi_{1}')
        self.check_args('/NumberField/1.1.1.1', r'\chi_{1}')

    def test_hard_degree10(self):
        self.check_args('/NumberField/10.10.1107649855354064.1', '10T36')
        self.check_args('/NumberField/10.10.138420300533025695415730492558689.1', '10T38')

    def test_hard_degree16(self):
        self.check_args('/NumberField/16.0.13307764731675384304522756096.1', '16T1535')

    def test_search_ramif_cl_deg(self):
        self.check_args('/NumberField/?degree=5&class_group=[2%2C2]&ur_primes=7&discriminant=&ram_quantifier=exactly&ram_primes=2%2C3%2C5', '5.1.27000000000.8')

    def test_abelian_conductor(self):
        self.check_args('/NumberField/5.5.5719140625.2', '275') # conductor

    def test_stuff_not_computed(self):
        self.check_args('/NumberField/23.23.931347256889446325436632107655346061164193665348344821578377438399536607931200329.1', 'ot computed')

    def test_search_poly_mean2parser(self):
        # X^3-4x+2
        self.check_args('/NumberField/?jump=X**3-4x%2B2&search=Go', '3.3.148.1') # label
        # z^3 - 4*z + 2
        self.check_args('/NumberField/?jump=z%5E3+-+4*z%2B2', '3.3.148.1') # label

    def test_search_zeta(self):
        self.check_args('/NumberField/?jump=Qzeta23&search=Go', '[3]') # class group
        self.check_args('/NumberField/?jump=Qzeta_23&search=Go', '[3]') # class group
        self.check_args('/NumberField/?jump=qzeta23%2B&search=Go', '1014.3133') # regulator
        self.check_args('/NumberField/?jump=qzeta_23%2B&search=Go', '1014.3133') # regulator

    def test_search_sqrt(self):
        self.check_args('/NumberField/?jump=Qsqrt-163&search=Go', '41') # minpoly
        self.check_args('/NumberField/?jump=q(sqrt-163)&search=Go', '41') # minpoly

    def test_search_multiple_fields(self):
        # Test comma-separated list of field labels
        self.check_args('/NumberField/?jump=2.2.5.1%2c+3.3.49.1&search=Go', '2.2.5.1')
        self.check_args('/NumberField/?jump=2.2.5.1%2c+3.3.49.1&search=Go', '3.3.49.1')
        # Test comma-separated list with different input formats
        self.check_args('/NumberField/?jump=Qsqrt5%2c+x%5E2-3&search=Go', '2.2.5.1')
        self.check_args('/NumberField/?jump=Qsqrt5%2c+x%5E2-3&search=Go', '2.2.12.1')

    def test_search_disc(self):
        self.check_args('/NumberField/?discriminant=1988-2014', '401') # factor of one of the discriminants

    def test_url_label(self):
        self.check_args('/NumberField/2.2.5.1', '0.481211825') # regulator

    # ---- Lean certificate download ----
    LEAN_LABEL = '5.1.3790297.2'
    LEAN_SMALL_LABEL = '2.2.5.1'

    def _skip_if_lean_field_absent(self):
        from lmfdb.number_fields.web_number_field import WebNumberField
        if WebNumberField(self.LEAN_LABEL).is_null():
            self.skipTest('%s not present in the test database' % self.LEAN_LABEL)

    def test_lean_certificate_link(self):
        # Fields with enough database data advertise an on-demand Lean certificate.
        self._skip_if_lean_field_absent()
        self.check_args('/NumberField/' + self.LEAN_LABEL,
                        ['Lean certificate', self.LEAN_LABEL + '/lean'])
        self.check_args('/NumberField/' + self.LEAN_SMALL_LABEL,
                        ['Lean certificate', self.LEAN_SMALL_LABEL + '/lean'])

    def test_lean_certificate_download(self):
        import io
        import zipfile
        self._skip_if_lean_field_absent()
        with tempfile.TemporaryDirectory() as cert_dir:
            entry_dir = os.path.join(
                cert_dir, 'IdealArithmetic', 'Examples', 'NF5_1_3790297_2')
            os.makedirs(entry_dir)
            open(os.path.join(cert_dir, 'lakefile.lean'), 'w').write('import Lake\n')
            open(os.path.join(cert_dir, 'lean-toolchain'), 'w').write('leanprover/lean4:v4.30.0-rc1\n')
            open(os.path.join(entry_dir, 'Results5_1_3790297_2.lean'), 'w').write(
                "theorem K_discr' : discr K = LMFDB_discriminant := K_discr\n"
                "theorem class_number_K_eq_4' : classNumber K = LMFDB_classNumber := class_number_K_eq_4\n")
            with patch('lmfdb.number_fields.lean_certificate.get_or_create_certificate_project',
                       return_value=cert_dir):
                r = self.tc.get('/NumberField/' + self.LEAN_LABEL + '/lean')
            assert r.status_code == 200
            assert r.mimetype == 'application/zip'
            assert 'attachment' in r.headers.get('Content-Disposition', '')
            zf = zipfile.ZipFile(io.BytesIO(r.get_data()))
            assert zf.testzip() is None
            names = zf.namelist()
            assert self.LEAN_LABEL + '/lakefile.lean' in names
            results = zf.read(self.LEAN_LABEL + '/IdealArithmetic/Examples/'
                              'NF5_1_3790297_2/Results5_1_3790297_2.lean').decode()
            assert 'discr K = 3790297' in results
            assert 'classNumber K = 4' in results
            assert 'WARNING' not in zf.read(self.LEAN_LABEL + '/README.txt').decode()

    def test_lean_certificate_generated_end_to_end(self):
        # For a small field the certificate is generated on the fly: the download
        # is a buildable Lake project whose entry point carries the interpolated
        # LMFDB values and is imported from the library root (so `lake build`
        # checks it).
        import io
        import zipfile
        with tempfile.TemporaryDirectory() as cache_root:
            with patch.dict(os.environ, {'LMFDB_LEAN_CERT_CACHE': cache_root}):
                r = self.tc.get('/NumberField/' + self.LEAN_SMALL_LABEL + '/lean')
            assert r.status_code == 200
            assert r.mimetype == 'application/zip'
            zf = zipfile.ZipFile(io.BytesIO(r.get_data()))
            assert zf.testzip() is None
            pre = self.LEAN_SMALL_LABEL + '/'
            root = zf.read(pre + 'IdealArithmetic.lean').decode()
            assert 'import IdealArithmetic.Examples.NF2_2_5_1.Results2_2_5_1' in root
            results = zf.read(
                pre + 'IdealArithmetic/Examples/NF2_2_5_1/Results2_2_5_1.lean').decode()
            assert 'discr K = 5' in results
            assert 'classNumber K = 1' in results
            assert pre + 'lakefile.lean' in zf.namelist()
            assert pre + 'lean-toolchain' in zf.namelist()

    def test_lean_certificate_absent(self):
        # Invalid labels and missing fields still do not have certificate downloads.
        assert self.tc.get('/NumberField/not-a-label/lean').status_code == 404
        assert self.tc.get('/NumberField/99.99.999.99/lean').status_code == 404

    def test_lean_certificate_infeasible(self):
        # A field whose Minkowski bound is beyond the feasibility threshold is not
        # advertised and its download endpoint refuses.
        from lmfdb import db
        label = db.nf_fields.lucky(
            {'degree': 2, 'disc_abs': {'$gt': 10**8}, 'class_number': {'$exists': True}},
            projection='label')
        if label is None:
            self.skipTest('no large-discriminant quadratic in the test database')
        self.not_check_args('/NumberField/' + label, 'Lean certificate')
        assert self.tc.get('/NumberField/' + label + '/lean').status_code == 404

    def test_lean_certificate_template_not_hardcoded(self):
        from lmfdb.number_fields.lean_certificate import lean_deinterpolate
        results = lean_deinterpolate(
            "theorem K_discr' : discr K = 3790297 := K_discr\n"
            "theorem class_number_K_eq_4' : classNumber K = 4 := class_number_K_eq_4\n")
        assert 'discr K = LMFDB_discriminant' in results
        assert 'classNumber K = LMFDB_classNumber' in results
        assert 'discr K = 3790297' not in results
        assert 'classNumber K = 4' not in results

    def test_url_naturallabel(self):
        self.check_args('/NumberField/Qsqrt5', '0.481211825') # regulator

    def test_url_naturallabel_custom(self):
        # Test various different custom nicknames for number fields
        self.check_args('/NumberField/Qi', '2.0.4.1')
        self.check_args('/NumberField/Qphi', '2.2.5.1')
        self.check_args('/NumberField/Qcbrt2', '3.1.108.1')
        self.check_args('/NumberField/Q(sqrt2+sqrt3)', '4.4.2304.1')
        self.check_args('/NumberField/Q(sqrt2,sqrt3)', '4.4.2304.1')
        self.check_args('/NumberField/Q(sqrt(1 + sqrt2))', '4.2.1024.1')
        self.check_args('/NumberField/Q(sqrt2,sqrt3,cbrt2)', '12.4.320979616137216.3')
        self.check_args('/NumberField/Q(sqrt2,-sqrt2)', '2.2.8.1')
        self.check_args('/NumberField/Q(sqrt2-sqrt2)', '1.1.1.1')

    def test_arith_equiv(self):
        self.check_args('/NumberField/7.3.6431296.1', '7.3.6431296.2') # arith equiv field

    def test_sextic_twin(self):
        self.check_args('/NumberField/6.0.10816.1', 'Twin sextic algebra')

    def test_how_computed(self):
        self.check_args('/NumberField/Source', 'Hunter searches')

    def test_galois_group_page(self):
        self.check_args('/NumberField/GaloisGroups', 'abstract group may have')

    def test_imaginary_quadratic_page(self):
        self.check_args('/NumberField/QuadraticImaginaryClassGroups', 'extensive computations')

    def test_discriminants_page(self):
        self.check_args('/NumberField/Source', 'Jones-David Roberts')

    def test_field_labels_page(self):
        self.check_args('/NumberField/FieldLabels', 'with the same signature and absolute value of the')

    def test_url_bad(self):
        self.check_args('/NumberField/junk', 'Error')  # error message

    def test_random_field(self):
        self.check_args('/NumberField/random', 'Discriminant')

    def test_statistics(self):
        self.check_args('/NumberField/stats', 'Class number')

    def test_pretty_labels(self):
        # Test "prettified" latex labels for number fields
        self.check_args('/NumberField/1.1.1.1', r'\Q')
        self.check_args('/NumberField/2.0.4.1', r'\Q(\sqrt{-1})')
        self.check_args('/NumberField/4.4.1600.1', r'\Q(\sqrt{2}, \sqrt{5})')
        self.check_args('/NumberField/6.0.16807.1', r'\Q(\zeta_{7})')
        self.check_args('/NumberField/3.3.49.1', r'\Q(\zeta_{7})^+')
        self.check_args('/NumberField/3.1.300.1', r'\Q(\sqrt[3]{10})')
        self.check_args('/NumberField/4.2.2048.1', r'\Q(\sqrt[4]{2})')
        self.check_args('/NumberField/4.0.512.1', r'\Q(\sqrt{1 + i})')
        self.check_args('/NumberField/4.2.1024.1', r'\Q(\sqrt{1 + \sqrt{2}})')
        self.check_args('/NumberField/4.0.2048.2', r'\Q(\sqrt{-2 + \sqrt{2}})')
        self.check_args('/NumberField/8.8.3317760000.1', r'\Q(\sqrt{2}, \sqrt{3}, \sqrt{5})')
        self.check_args('/NumberField/16.0.11007531417600000000.1', r'\Q(i, \sqrt{2}, \sqrt{3}, \sqrt{5})')
        self.check_args('/NumberField/32.0.4026692887688564776141139207792885760000000000000000.1', r'\Q(i, \sqrt{2}, \sqrt{3}, \sqrt{5}, \sqrt{7})')

    def test_signature_search(self):
        # Square brackets
        self.check_args('/NumberField/?start=0&degree=6&signature=%5B0%2C3%5D&count=100', '6.0.61131.1')
        self.check_args('/NumberField/?start=0&degree=7&signature=%5B3%2C2%5D&count=100', '7.3.1420409.1')
        # Round brackets
        self.check_args('/NumberField/?start=0&degree=6&signature=%280%2C3%29&count=100', '6.0.61131.1')
        self.check_args('/NumberField/?start=0&degree=7&signature=%283%2C2%29&count=100', '7.3.1420409.1')

    def test_signature_display(self):
        # Verify that signatures are displayed with parentheses, not square brackets
        self.check_args('/NumberField/6.0.61131.1', '(0, 3)')  # degree 6 field with signature (0, 3)
        self.check_args('/NumberField/7.3.1420409.1', '(3, 2)')  # degree 7 field with signature (3, 2)

    def test_relative_class_number(self):
        self.check_args('/NumberField/4.0.1327873600.2', '2108')

    def test_fundamental_units(self):
        self.check_args('NumberField/2.2.10069.1', '43388173')
        self.check_args('NumberField/3.3.10004569.1', '22153437467081345')

    def test_split_ors(self):
        self.check_args('/NumberField/?signature=%5B0%2C3%5D&galois_group=S3', '6.0.177147.2')
        self.check_args('/NumberField/?signature=%5B3%2C0%5D&galois_group=S3', '3.3.229.1')
        self.check_args('/NumberField/?signature=[4%2C0]&galois_group=C2xC2&class_number=3%2C6','4.4.1311025.1')
        self.check_args('/NumberField/?signature=[4%2C0]&galois_group=C2xC2&class_number=6%2C3','4.4.1311025.1')
        self.check_args('/NumberField/?signature=[4%2C0]&galois_group=C2xC2&class_number=5-6%2C3','4.4.485809.1')

    def test_underlying_data(self):
        self.check_args('NumberField/2.2.10069.1', ['Underlying data', 'data/2.2.10069.1'])

    def test_errors(self):
        self.check_args('NumberField/18.0.10490638424...4432.1/download/sage', 'Invalid label')
        self.check_args('NumberField/4.3.2.1/download/sage', 'There is no number field with label 4.3.2.1')

    def test_signature_download(self):
        # Test that signature is downloaded as [r1, r2] not [r2, degree]
        # For degree 2 fields with negative discriminant: signature is [0, 1] (complex)
        # For degree 2 fields with positive discriminant: signature is [2, 0] (real)
        url = ('/NumberField/?download=1'
               '&query=%7B%27degree%27%3A+2%2C+%27%24or%27%3A+%5B%7B%27disc_sign%27%3A+'
               '-1%2C+%27disc_abs%27%3A+%7B%27%24gte%27%3A+1%2C+%27%24lte%27%3A+3%7D%2C+'
               '%27degree%27%3A+2%7D%2C+%7B%27disc_sign%27%3A+1%2C+%27disc_abs%27%3A+'
               '%7B%27%24lte%27%3A+5%2C+%27%24gte%27%3A+1%7D%2C+%27degree%27%3A+2%7D%5D%7D'
               '&degree=2&discriminant=-3-5&showcol=signature&Submit=text')
        page = self.tc.get(url).get_data(as_text=True)
        # Check that signature format is [r1, r2] where:
        # - For imaginary quadratic fields (disc < 0, degree=2): r1=0, r2=1, so signature=[0, 1]
        # - For real quadratic fields (disc > 0, degree=2): r1=2, r2=0, so signature=[2, 0]
        # The bug was that it showed [r2, degree] = [1, 2] or [0, 2] instead
        assert '[0, 1]' in page  # imaginary quadratic field (with space, no quotes)
        assert '[2, 0]' in page  # real quadratic field (with space, no quotes)
        # Make sure we're NOT getting the buggy format [r2, degree]
        assert '[1, 2]' not in page  # wrong format for imaginary quadratic
        assert '[0, 2]' not in page  # wrong format for real quadratic
        # Also ensure we're not getting quoted strings
        assert '"[0, 1]"' not in page
        assert '"[2, 0]"' not in page
