// Code generated by depstubber. DO NOT EDIT.
// This is a simple stub for github.com/golang-jwt/jwt/v5, strictly for use in testing.

// See the LICENSE file for information about the licensing of the original library.
// Source: github.com/golang-jwt/jwt/v5 (exports: RegisteredClaims,Parser,Token; functions: Parse,ParseWithClaims)

// Package jwt is a stub of github.com/golang-jwt/jwt/v5, generated by depstubber.
package jwt

import (
	time "time"
)

type ClaimStrings []string

func (_ ClaimStrings) MarshalJSON() ([]byte, error) {
	return nil, nil
}

func (_ *ClaimStrings) UnmarshalJSON(_ []byte) error {
	return nil
}

type Claims interface {
	GetAudience() (ClaimStrings, error)
	GetExpirationTime() (*NumericDate, error)
	GetIssuedAt() (*NumericDate, error)
	GetIssuer() (string, error)
	GetNotBefore() (*NumericDate, error)
	GetSubject() (string, error)
}

type Keyfunc func(*Token) (interface{}, error)

type NumericDate struct {
	Time time.Time
}

func (_ NumericDate) Add(_ time.Duration) time.Time {
	return time.Time{}
}

func (_ NumericDate) AddDate(_ int, _ int, _ int) time.Time {
	return time.Time{}
}

func (_ NumericDate) After(_ time.Time) bool {
	return false
}

func (_ NumericDate) AppendFormat(_ []byte, _ string) []byte {
	return nil
}

func (_ NumericDate) Before(_ time.Time) bool {
	return false
}

func (_ NumericDate) Clock() (int, int, int) {
	return 0, 0, 0
}

func (_ NumericDate) Compare(_ time.Time) int {
	return 0
}

func (_ NumericDate) Date() (int, time.Month, int) {
	return 0, 0, 0
}

func (_ NumericDate) Day() int {
	return 0
}

func (_ NumericDate) Equal(_ time.Time) bool {
	return false
}

func (_ NumericDate) Format(_ string) string {
	return ""
}

func (_ NumericDate) GoString() string {
	return ""
}

func (_ NumericDate) GobEncode() ([]byte, error) {
	return nil, nil
}

func (_ NumericDate) Hour() int {
	return 0
}

func (_ NumericDate) ISOWeek() (int, int) {
	return 0, 0
}

func (_ NumericDate) In(_ *time.Location) time.Time {
	return time.Time{}
}

func (_ NumericDate) IsDST() bool {
	return false
}

func (_ NumericDate) IsZero() bool {
	return false
}

func (_ NumericDate) Local() time.Time {
	return time.Time{}
}

func (_ NumericDate) Location() *time.Location {
	return nil
}

func (_ NumericDate) MarshalBinary() ([]byte, error) {
	return nil, nil
}

func (_ NumericDate) MarshalJSON() ([]byte, error) {
	return nil, nil
}

func (_ NumericDate) MarshalText() ([]byte, error) {
	return nil, nil
}

func (_ NumericDate) Minute() int {
	return 0
}

func (_ NumericDate) Month() time.Month {
	return 0
}

func (_ NumericDate) Nanosecond() int {
	return 0
}

func (_ NumericDate) Round(_ time.Duration) time.Time {
	return time.Time{}
}

func (_ NumericDate) Second() int {
	return 0
}

func (_ NumericDate) String() string {
	return ""
}

func (_ NumericDate) Sub(_ time.Time) time.Duration {
	return 0
}

func (_ NumericDate) Truncate(_ time.Duration) time.Time {
	return time.Time{}
}

func (_ NumericDate) UTC() time.Time {
	return time.Time{}
}

func (_ NumericDate) Unix() int64 {
	return 0
}

func (_ NumericDate) UnixMicro() int64 {
	return 0
}

func (_ NumericDate) UnixMilli() int64 {
	return 0
}

func (_ NumericDate) UnixNano() int64 {
	return 0
}

func (_ NumericDate) Weekday() time.Weekday {
	return 0
}

func (_ NumericDate) Year() int {
	return 0
}

func (_ NumericDate) YearDay() int {
	return 0
}

func (_ NumericDate) Zone() (string, int) {
	return "", 0
}

func (_ NumericDate) ZoneBounds() (time.Time, time.Time) {
	return time.Time{}, time.Time{}
}

func (_ *NumericDate) GobDecode(_ []byte) error {
	return nil
}

func (_ *NumericDate) UnmarshalBinary(_ []byte) error {
	return nil
}

func (_ *NumericDate) UnmarshalJSON(_ []byte) error {
	return nil
}

func (_ *NumericDate) UnmarshalText(_ []byte) error {
	return nil
}

func Parse(_ string, _ Keyfunc, _ ...ParserOption) (*Token, error) {
	return nil, nil
}

func ParseWithClaims(_ string, _ Claims, _ Keyfunc, _ ...ParserOption) (*Token, error) {
	return nil, nil
}

type Parser struct{}

func (_ *Parser) DecodeSegment(_ string) ([]byte, error) {
	return nil, nil
}

func (_ *Parser) Parse(_ string, _ Keyfunc) (*Token, error) {
	return nil, nil
}

func (_ *Parser) ParseUnverified(_ string, _ Claims) (*Token, []string, error) {
	return nil, nil, nil
}

func (_ *Parser) ParseWithClaims(_ string, _ Claims, _ Keyfunc) (*Token, error) {
	return nil, nil
}

type ParserOption func(*Parser)

type RegisteredClaims struct {
	Issuer    string
	Subject   string
	Audience  ClaimStrings
	ExpiresAt *NumericDate
	NotBefore *NumericDate
	IssuedAt  *NumericDate
	ID        string
}

func (_ RegisteredClaims) GetAudience() (ClaimStrings, error) {
	return nil, nil
}

func (_ RegisteredClaims) GetExpirationTime() (*NumericDate, error) {
	return nil, nil
}

func (_ RegisteredClaims) GetIssuedAt() (*NumericDate, error) {
	return nil, nil
}

func (_ RegisteredClaims) GetIssuer() (string, error) {
	return "", nil
}

func (_ RegisteredClaims) GetNotBefore() (*NumericDate, error) {
	return nil, nil
}

func (_ RegisteredClaims) GetSubject() (string, error) {
	return "", nil
}

type SigningMethod interface {
	Alg() string
	Sign(_ string, _ interface{}) ([]byte, error)
	Verify(_ string, _ []byte, _ interface{}) error
}

type Token struct {
	Raw       string
	Method    SigningMethod
	Header    map[string]interface{}
	Claims    Claims
	Signature []byte
	Valid     bool
}

func (_ *Token) EncodeSegment(_ []byte) string {
	return ""
}

func (_ *Token) SignedString(_ interface{}) (string, error) {
	return "", nil
}

func (_ *Token) SigningString() (string, error) {
	return "", nil
}
